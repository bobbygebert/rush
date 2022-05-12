{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module IR where

import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.List hiding (concat)
import qualified Data.Map as Map
import qualified Data.Map.Ordered as OMap
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, length, unwords, zip)
import qualified Data.Text as Text
import Infer
import Span
import Text.PrettyPrint
import Prelude hiding (concat, const, (++), (<>))

data Constant t
  = CNum Text t
  | CData Text t [Constant t]
  | CFn t (Text, t) (Expr t)
  deriving (Eq, Functor, Foldable)

instance (Show t) => Show (Constant t) where
  show = \case
    CNum n _ -> unpack n
    CData n ty xs ->
      show $
        Data n ty (OMap.fromList $ zip (pack . show <$> [0 ..]) (unConst <$> xs))
    CFn tc (x, tx) b ->
      show tc ++ " (" ++ unpack x ++ ": " ++ show tx ++ ") -> " ++ show b

data Named t = Named Text (Constant t)
  deriving (Show, Eq, Functor)

data Type
  = TInt
  | TTup [Type]
  | TList Type
  | TData Text [(Text, OMap.OMap Text Type)]
  | TRef Text
  | TVar Text
  | TCallable Type Type
  | TFn Type Type Type
  | TUnit
  | Kind
  deriving (Eq, Ord)

instance Show Type where
  show = renderStyle (style {lineLength = 100000}) . tdoc

data Expr t
  = Num Text t
  | Var Text t
  | Add (Expr t) (Expr t)
  | Sub (Expr t) (Expr t)
  | Mul (Expr t) (Expr t)
  | Div (Expr t) (Expr t)
  | Mod (Expr t) (Expr t)
  | Unit
  | Tup [Expr t]
  | List t [Expr t]
  | Cons (Expr t) (Expr t)
  | Data Text t (OMap.OMap Text (Expr t))
  | Match [Expr t] [([Expr t], Expr t)]
  | Fn t (Text, t) (Expr t)
  | App t (Expr t) (Expr t)
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show t) => Show (Expr t) where
  show = renderStyle (style {lineLength = 100000}) . vdoc

tdoc = \case
  TInt {} -> text "Int"
  TUnit -> text "()"
  TTup xs -> parens $ cat $ punctuate comma (tdoc <$> xs)
  TList tx -> brackets $ tdoc tx
  TVar v -> text "'" <> text (unpack v)
  TData n _ -> text $ unpack n
  TRef n -> text $ unpack n
  TFn cls tx tb -> parens $ tdoc cls <+> tdoc tx <+> text "->" <+> tdoc tb
  TCallable tx tb -> parens $ tdoc tx <+> text "->" <+> tdoc tb
  Kind -> "*"

vdoc :: (Show t) => Expr t -> Doc
vdoc = \case
  Num n _ -> text $ unpack n
  Var v ty -> parens $ text (unpack v) <> colon <+> text (show ty)
  Add a b -> showBinOp "+" a b
  Sub a b -> showBinOp "-" a b
  Mul a b -> showBinOp "*" a b
  Div a b -> showBinOp "/" a b
  Mod a b -> showBinOp "%" a b
  Unit -> text "()"
  Tup xs -> parens $ cat $ punctuate comma (vdoc <$> xs)
  List _ xs -> brackets $ cat $ punctuate comma (vdoc <$> xs)
  Cons h t -> parens $ vdoc h <+> "::" <+> cons t
    where
      cons (Cons x xs) = vdoc x <+> "::" <+> cons xs
      cons x = vdoc x
  Data n _ fs
    | OMap.size fs == 0 -> text $ unpack n
    | otherwise ->
      parens $
        text (unpack n)
          <+> cat
            ( punctuate
                (comma <> space)
                ((\(k, v) -> parens $ text (unpack k) <> colon <+> vdoc v) <$> OMap.assocs fs)
            )
  Match xs ps ->
    hang (text "match" <+> cat (vdoc <$> xs)) 2 $
      braces $
        cat (punctuate comma (showArm <$> ps))
    where
      showArm (ps, b) = cat (parens . text . show <$> ps) <+> text "->" <+> vdoc b
  Fn cls (x, tx) b ->
    parens $
      braces (text $ show cls)
        <+> parens (text (unpack x) <> colon <+> text (show tx))
        <+> "->"
        <+> vdoc b
  App ty f x -> parens $ parens (vdoc f <+> vdoc x) <> colon <+> text (show ty)

showBinOp op a b = parens $ vdoc a <+> op <+> vdoc b

instance Template Type where
  freeTypeVars = \case
    TInt -> Set.empty
    TUnit -> Set.empty
    TTup tys -> foldr (Set.union . freeTypeVars) Set.empty tys
    TList tx -> freeTypeVars tx
    TVar v -> Set.singleton v
    TFn cls a b -> freeTypeVars cls `Set.union` freeTypeVars a `Set.union` freeTypeVars b
    TCallable a b -> freeTypeVars a `Set.union` freeTypeVars b
    TData _ _ -> Set.empty
    TRef _ -> Set.empty
    Kind -> Set.empty

  instantiate ty = do
    let vs = Set.toList $ freeTypeVars ty
    vs' <- replicateM (length vs) (fresh emptySpan)
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ case ty of
      TInt {} -> ty
      TUnit -> ty
      TTup tys -> TTup $ apply s <$> tys
      TList tx -> TList $ apply s tx
      TVar {} -> ty
      TFn cls a b -> TFn (apply s cls) (apply s a) (apply s b)
      TCallable a b -> TCallable (apply s a) (apply s b)
      TData n cs -> TData n cs
      TRef n -> TRef n
      Kind -> Kind

instance Refine Type Type where
  apply ss@(Substitutions ss') = \case
    t@TInt {} -> t
    TUnit -> TUnit
    TTup tys -> TTup $ apply ss <$> tys
    TList tx -> TList $ apply ss tx
    t@(TVar v) -> Map.findWithDefault t v ss'
    TFn cls as b -> TFn (apply ss cls) (apply ss as) (apply ss b)
    TCallable as b -> TCallable (apply ss as) (apply ss b)
    TData n cs -> TData n cs
    TRef n -> TRef n
    Kind -> Kind

instance Unify Type where
  unifyingSubstitutions a b = usubs a b
    where
      usubs t t' | t == t' = return $ Substitutions Map.empty
      usubs (TTup txs) (TTup tys) = unifyMany txs tys
      usubs (TList tx) (TList ty) = unifyingSubstitutions tx ty
      usubs (TVar v) TCallable {} = return $ Substitutions Map.empty
      usubs (TVar v) t = v `bind` t
      usubs a b@TVar {} = usubs b a
      usubs t1@TRef {} t2@TData {} = usubs t2 t1
      usubs (TData n _) (TRef n') | n == n' = return $ Substitutions Map.empty
      usubs (TFn tc tx tb) (TFn tc' tx' tb') = unifyMany [tc, tx, tb] [tc', tx', tb']
      usubs tf@TFn {} tc@TData {} = usubs tc tf
      usubs tc@TData {} tf@(TFn tc' _ _) = usubs tc tc'
      usubs TData {} TCallable {} = return $ Substitutions Map.empty
      usubs TCallable {} TData {} = return $ Substitutions Map.empty
      usubs (TCallable a b) (TCallable a' b') = unifyMany [a, b] [a', b']
      usubs a b@TCallable {} = usubs b a
      usubs (TCallable a b) (TFn _ a' b') = unifyMany [a, b] [a', b']
      usubs t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv) = v == tv
  isVar _ _ = False

unConst :: Constant t -> Expr t
unConst = \case
  CFn tc x b -> Fn tc x b
  CNum n ty -> Num n ty
  CData c ty fs ->
    Data c ty (OMap.fromList $ zip (pack . show <$> [0 ..]) (unConst <$> fs))

const :: Expr t -> Constant t
const = \case
  Fn tc x b -> CFn tc x b
  Data c ty xs -> CData c ty (const . snd <$> OMap.assocs xs)
  Num n ty -> CNum n ty
  _ -> error "unreachable"

typeOf :: Expr Type -> Type
typeOf = \case
  Num _ ty -> ty
  Var _ ty -> ty
  Add a _ -> typeOf a
  Sub a _ -> typeOf a
  Mul a _ -> typeOf a
  Div a _ -> typeOf a
  Mod a _ -> typeOf a
  Unit -> TUnit
  Tup xs -> TTup $ typeOf <$> xs
  List tx _ -> TList tx
  Cons h _ -> TList (typeOf h)
  Data _ ty _ -> ty
  Match xs ((ps, b) : _) -> typeOf b
  Match _ _ -> error "unreachable"
  Fn cls a b -> TFn cls (snd a) (typeOf b)
  App ty f x -> ty
