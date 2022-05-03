{-# LANGUAGE DeriveFunctor #-}
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

data Type
  = TInt Span
  | TTup [Type]
  | TVar Text Span
  | TStruct (Map.Map Text Type)
  | TClosure Text (Map.Map Text Type) Type
  | TUnit
  | TFn Type Type Type
  deriving (Eq)

data Expr t
  = Num Text t
  | Unit
  | Tup [Expr t]
  | Var Text t
  | Add (Expr t) (Expr t)
  | Match [Expr t] [([Pattern.Pattern t], Expr t)]
  | Fn Text Type (Text, t) (Expr t)
  | Closure Text (Map.Map Text (Expr t)) (Expr t)
  | App t (Expr t) (Expr t)
  deriving (Eq, Functor)

instance Show Type where
  show = \case
    TInt {} -> "Int"
    TUnit -> "()"
    TTup xs -> "(" ++ intercalate "," (show <$> xs) ++ ")"
    TVar v _ -> unpack v
    TStruct fields ->
      "{ " ++ intercalate ", " (showField <$> Map.toList fields) ++ " }"
      where
        showField (x, tx) = unpack x ++ " = " ++ show tx
    TFn cls x tb -> "{" ++ show cls ++ "} " ++ show x ++ " -> " ++ show tb
    TClosure f cs _ -> show (TStruct cs) ++ " " ++ unpack f

instance (Show t) => Show (Expr t) where
  show = \case
    Num n _ -> unpack n
    Unit -> "()"
    Tup xs -> "(" ++ intercalate "," (show <$> xs) ++ ")"
    Var v _ -> unpack v
    Add a b -> "(" ++ show a ++ " + " ++ show b ++ ")"
    Match xs ps ->
      "(match " ++ unwords (("(" ++) . (++ ")") . show <$> xs) ++ " { "
        ++ intercalate ", " (showArm <$> ps)
        ++ " })"
      where
        showArm (ps, b) = unwords (("(" ++) . (++ ")") . show <$> ps) ++ " -> " ++ show b
    Fn _ cls (x, tx) tb -> "(f = {" ++ show cls ++ "} (" ++ unpack x ++ ": " ++ show tx ++ ") -> " ++ show tb ++ ")"
    Closure f fields _ ->
      "({" ++ intercalate ", " (showCapture <$> Map.toList fields) ++ "} "
        ++ unpack f
        ++ ")"
      where
        showCapture (x, e) = unpack x ++ " = " ++ show e
    App _ f x -> "(" ++ show f ++ " " ++ show x ++ ")"

instance Template Type where
  freeTypeVars = \case
    TInt _ -> Set.empty
    TUnit -> Set.empty
    TTup tys -> foldr (Set.union . freeTypeVars) Set.empty tys
    TVar v _ -> Set.singleton v
    TStruct fields -> foldr (Set.union . freeTypeVars) Set.empty (Map.elems fields)
    TClosure _ c f -> freeTypeVars c `Set.union` freeTypeVars f
    TFn cls a b -> freeTypeVars cls `Set.union` freeTypeVars a `Set.union` freeTypeVars b

  instantiate ty = do
    let vs = Set.toList $ freeTypeVars ty
    vs' <- forM vs $ const (fresh (spanOf ty))
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ case ty of
      TInt {} -> ty
      TUnit -> ty
      TTup tys -> TTup $ apply s <$> tys
      TVar {} -> ty
      TStruct fields -> TStruct $ Map.map (apply s) fields
      TClosure f c t -> TClosure f c (apply s t)
      TFn cls a b -> TFn (apply s cls) (apply s a) (apply s b)

instance Refinable Type Type where
  apply ss@(Substitutions ss') = \case
    t@TInt {} -> t
    TUnit -> TUnit
    TTup tys -> TTup $ apply ss <$> tys
    t@(TVar v s) -> withSpan s (Map.findWithDefault t v ss')
    TStruct fields -> TStruct $ apply ss <$> fields
    TClosure f c b -> TClosure f (apply ss c) (apply ss b)
    TFn cls as b -> TFn (apply ss cls) (apply ss as) (apply ss b)

instance Unifiable Type where
  unifyingSubstitutions t t' | withSpan emptySpan t == withSpan emptySpan t' = return $ Substitutions Map.empty
  unifyingSubstitutions (TTup txs) (TTup tys) = unifyMany txs tys
  unifyingSubstitutions (TVar v _) t = v `bind` t
  unifyingSubstitutions t (TVar v _) = v `bind` t
  unifyingSubstitutions (TStruct fields) (TStruct fields') =
    unifyMany (snd <$> Map.toAscList fields) (snd <$> Map.toAscList fields')
  unifyingSubstitutions ty@(TClosure f c b) ty'@(TClosure f' c' b') =
    unifyMany (b : Map.elems c) (b' : Map.elems c')
  unifyingSubstitutions tf@TFn {} tc@TClosure {} = unifyingSubstitutions tc tf
  unifyingSubstitutions tc@(TClosure _ _ tf) tf'@(TFn tc' _ _) =
    unifyMany [tf, tc] [tf', tc']
  unifyingSubstitutions (TFn cls a b) (TFn cls' a' b') = unifyMany [cls, a, b] [cls', a', b']
  unifyingSubstitutions t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv _) = v == tv
  isVar _ _ = False

typeOf :: Expr Type -> Type
typeOf = \case
  Num _ ty -> ty
  Unit -> TUnit
  Tup xs -> TTup $ typeOf <$> xs
  Var _ ty -> ty
  Add a _ -> typeOf a
  Match xs ((ps, b) : _) -> typeOf b
  Match _ _ -> error "unreachable"
  Fn name cls a b -> TFn cls (snd a) (typeOf b)
  Closure name c f -> TClosure name (Map.map typeOf c) (typeOf f)
  App ty f x -> ty

-- TODO: Merge Spans
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TTup tys -> spanOf $ head tys
  TVar _ s -> s
  TStruct _ -> emptySpan
  TClosure _ c tf -> spanOf tf
  TFn _ a b -> spanOf a
  TUnit -> emptySpan

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TTup tys -> TTup $ withSpan s <$> tys
  TVar v _ -> TVar v s
  TStruct fields -> TStruct $ withSpan s <$> fields
  TClosure f c tf -> TClosure f (Map.map (withSpan s) c) (withSpan s tf)
  TFn cls a b -> TFn (withSpan s cls) (withSpan s a) (withSpan s b)
  TUnit -> TUnit
