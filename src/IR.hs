{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module IR where

import Control.Monad
import Control.Monad.Except
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, unwords, zip)
import Infer
import Parser (Span, as, emptySpan)
import qualified Pattern
import Text.PrettyPrint
import Prelude hiding ((<>))

data Constant t
  = CNum Text t
  | CFn t (Text, t) (Expr t)
  deriving (Eq, Functor, Foldable)

instance (Show t) => Show (Constant t) where
  show = \case
    CNum n _ -> unpack n
    CFn tc (x, tx) b -> show tc ++ " (" ++ unpack x ++ ": " ++ show tx ++ ") -> " ++ show b

data Named t = Named Text (Constant t)
  deriving (Show, Eq, Functor)

data Type
  = TInt Span
  | TTup [Type]
  | TList Type
  | TVar Text Span
  | TStruct (Map.Map Text Type)
  | TUnion (Map.Map Text Type)
  | TClosure Text (Map.Map Text Type) Type
  | TUnit
  | TFn Type Type Type
  deriving (Eq, Ord)

data Expr t
  = Num Text t
  | Unit
  | Tup [Expr t]
  | List t [Expr t]
  | Cons (Expr t) (Expr t)
  | Var Text t
  | Add (Expr t) (Expr t)
  | Match [Expr t] [([Pattern.Pattern t], Expr t)]
  | Fn Type (Text, t) (Expr t)
  | Closure Text (Map.Map Text (Expr t)) (Expr t)
  | Union (Map.Map Text Type) Text (Expr t)
  | App t (Expr t) (Expr t)
  deriving (Eq, Functor, Foldable, Traversable)

instance Show Type where
  show = renderStyle (style {lineLength = 100000}) . tdoc

tdoc = \case
  TInt {} -> text "Int"
  TUnit -> text "()"
  TTup xs -> parens $ cat $ punctuate comma (tdoc <$> xs)
  TList tx -> brackets $ tdoc tx
  TVar v _ -> text "'" <> text (unpack v)
  TStruct fields -> braces $ nest 2 $ cat $ punctuate comma (showField <$> Map.toList fields)
    where
      showField (x, tx) = text (unpack x) <> colon <+> tdoc tx
  TUnion fields -> braces $ nest 2 $ cat $ punctuate (text " |") (nest 2 . showField <$> Map.toList fields)
    where
      showField (x, tx) = text (unpack x) <+> colon <+> tdoc tx
  TFn cls tx tb -> parens $ tdoc cls <+> tdoc tx <+> text "->" <+> tdoc tb
  TClosure f cs tf -> parens $ tdoc (TStruct cs) <+> text (unpack f) <> colon <+> tdoc tf

instance (Show t) => Show (Expr t) where
  show = renderStyle (style {lineLength = 100000}) . vdoc

vdoc :: (Show t) => Expr t -> Doc
vdoc = \case
  Num n _ -> text $ unpack n
  Unit -> text "()"
  Tup xs -> parens $ cat $ punctuate comma (vdoc <$> xs)
  List _ xs -> brackets $ cat $ punctuate comma (vdoc <$> xs)
  Cons h t -> parens $ vdoc h <+> "::" <+> cons t
    where
      cons (Cons x xs) = vdoc x <+> "::" <+> cons xs
      cons x = vdoc x
  Var v ty -> parens $ text (unpack v) <> colon <+> text (show ty)
  Add a b -> parens $ vdoc a <+> char '+' <+> vdoc b
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
  Closure name fields f ->
    parens $
      braces (cat $ punctuate comma (showCapture <$> Map.toList fields))
        <+> vdoc f
    where
      showCapture (x, e) = text (unpack x) <+> "=" <+> vdoc e
  Union ty disc val -> text (show ty) <> "." <> text (unpack disc) <> "@" <> vdoc val
  App ty f x -> parens $ parens (vdoc f <+> vdoc x) <> colon <+> text (show ty)

instance Template Type where
  freeTypeVars = \case
    TInt _ -> Set.empty
    TUnit -> Set.empty
    TTup tys -> foldr (Set.union . freeTypeVars) Set.empty tys
    TList tx -> freeTypeVars tx
    TVar v _ -> Set.singleton v
    TStruct fields -> foldr (Set.union . freeTypeVars) Set.empty (Map.elems fields)
    TClosure _ c f ->
      foldr (Set.union . freeTypeVars) Set.empty (Map.elems c)
        `Set.union` freeTypeVars f
    TUnion tys -> foldr (Set.union . freeTypeVars) Set.empty (Map.elems tys)
    TFn cls a b -> freeTypeVars cls `Set.union` freeTypeVars a `Set.union` freeTypeVars b

  instantiate ty = do
    let vs = Set.toList $ freeTypeVars ty
    vs' <- forM vs $ const (fresh (spanOf ty))
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ case ty of
      TInt {} -> ty
      TUnit -> ty
      TTup tys -> TTup $ apply s <$> tys
      TList tx -> TList $ apply s tx
      TVar {} -> ty
      TStruct fields -> TStruct $ Map.map (apply s) fields
      TUnion tys -> TStruct $ Map.map (apply s) tys
      TClosure f c t -> TClosure f c (apply s t)
      TFn cls a b -> TFn (apply s cls) (apply s a) (apply s b)

instance Refine Type Type where
  apply ss@(Substitutions ss') = \case
    t@TInt {} -> t
    TUnit -> TUnit
    TTup tys -> TTup $ apply ss <$> tys
    TList tx -> TList $ apply ss tx
    t@(TVar v s) -> withSpan s (Map.findWithDefault t v ss')
    TStruct fields -> TStruct $ apply ss <$> fields
    TUnion tys -> TUnion $ apply ss <$> tys
    TClosure f c b -> TClosure f (apply ss c) (apply ss b)
    TFn cls as b -> TFn (apply ss cls) (apply ss as) (apply ss b)

instance Unify Type where
  unifyingSubstitutions a b = usubs a b
    where
      usubs t t' | withSpan emptySpan t == withSpan emptySpan t' = return $ Substitutions Map.empty
      usubs (TTup txs) (TTup tys) = unifyMany txs tys
      usubs (TList tx) (TList ty) = unifyingSubstitutions tx ty
      usubs (TVar v _) t = v `bind` t
      usubs t (TVar v _) = v `bind` t
      usubs (TStruct fields) (TStruct fields') =
        unifyMany (snd <$> Map.toAscList fields) (snd <$> Map.toAscList fields')
      usubs ty@(TClosure f c b) ty'@(TClosure f' c' b') =
        unifyMany (b : Map.elems c) (b' : Map.elems c')
      usubs tf@TFn {} tc@TClosure {} = usubs tc tf
      usubs (TClosure _ cs tf) tf'@(TFn tc' _ _) =
        unifyMany [tf, TStruct cs] [tf', tc']
      usubs (TFn tc tx tb) (TFn tc' tx' tb') = unifyMany [tc, tx, tb] [tc', tx', tb']
      usubs tf@TFn {} tc@TUnion {} = usubs tc tf
      usubs (TUnion tcs) tf@TFn {} = do
        let tc' = TUnion $ Map.map toStruct tcs
        let tfs' = toFn tc' <$> Map.elems tcs
        uncurry unifyMany $ unzip (zip tfs' (repeat tf))
        where
          toStruct (TClosure _ cs _) = TStruct cs
          toStruct _ = error "unreachable"
          toFn tc (TClosure _ _ (TFn _ tx tb)) = TFn tc tx tb
          toFn _ _ = error "unreachable"
      usubs t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv _) = v == tv
  isVar _ _ = False

unConst :: Constant Type -> Expr Type
unConst = \case
  CFn tc x b -> Fn tc x b
  CNum n ty -> Num n ty

typeOf :: Expr Type -> Type
typeOf = \case
  Num _ ty -> ty
  Unit -> TUnit
  Tup xs -> TTup $ typeOf <$> xs
  List tx _ -> TList tx
  Cons h _ -> TList (typeOf h)
  Var _ ty -> ty
  Add a _ -> typeOf a
  Match xs ((ps, b) : _) -> typeOf b
  Match _ _ -> error "unreachable"
  Fn cls a b -> TFn cls (snd a) (typeOf b)
  Closure name c f -> TClosure name (Map.map typeOf c) (typeOf f)
  Union ty disc val -> TUnion ty
  App ty f x -> ty

typeOfP :: Pattern.Pattern Type -> Type
typeOfP = \case
  Pattern.Binding _ ty -> ty
  Pattern.Num _ ty -> ty
  Pattern.Tup pats -> TTup $ typeOfP <$> pats
  Pattern.List ty _ -> TList ty
  Pattern.Cons h _ -> TList (typeOfP h)

-- TODO: Merge Spans
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TTup tys -> spanOf $ head tys
  TList tx -> spanOf tx
  TVar _ s -> s
  TStruct _ -> emptySpan
  TUnion _ -> emptySpan
  TClosure _ c tf -> spanOf tf
  TFn _ a b -> spanOf a
  TUnit -> emptySpan

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TTup tys -> TTup $ withSpan s <$> tys
  TList tx -> TList $ withSpan s tx
  TVar v _ -> TVar v s
  TStruct fields -> TStruct $ withSpan s <$> fields
  TUnion tys -> TUnion $ withSpan s <$> tys
  TClosure f c tf -> TClosure f (Map.map (withSpan s) c) (withSpan s tf)
  TFn cls a b -> TFn (withSpan s cls) (withSpan s a) (withSpan s b)
  TUnit -> TUnit
