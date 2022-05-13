{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Type (spanOf, withSpan, Type (..)) where

import Control.Monad
import Control.Monad.Except
import Data.List hiding (lookup, span)
import qualified Data.List as List hiding (lookup, span)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, null, span, unlines, zip)
import GHC.RTS.Flags (ProfFlags (descrSelector))
import Infer
import Span

data Type
  = TInt Span
  | TTup [Type]
  | TList Type
  | TVar Text Span
  | TData Text Span [(Text, Span, [Type])]
  | TRef Text Span
  | Type :-> Type
  | Kind Span
  deriving (Eq)

instance Show Type where
  show = \case
    TInt _ -> "Int"
    TTup xs -> "(" ++ intercalate ", " (show <$> xs) ++ ")"
    TList tx -> "[" ++ show tx ++ "]"
    TVar txt _ -> "'" ++ unpack txt
    TData n _ _ -> unpack n
    TRef n _ -> unpack n
    a :-> b -> a' ++ " -> " ++ show b
      where
        a' = case a of
          c :-> d -> "(" ++ show a ++ ")"
          _ -> show a
    Kind {} -> "*"

infixr 9 :->

-- TODO: Merge Spans
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TTup tys -> spanOf $ head tys
  TList tx -> spanOf tx
  TVar _ s -> s
  TData _ s _ -> s
  TRef _ s -> s
  a :-> b -> spanOf a
  Kind s -> s

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TTup tys -> TTup $ withSpan s <$> tys
  TList tx -> TList $ withSpan s tx
  TVar v _ -> TVar v s
  TData n _ cs -> TData n s $ (\(c, _, ts) -> (c, s, withSpan s <$> ts)) <$> cs
  TRef n _ -> TRef n s
  a :-> b -> withSpan s a :-> withSpan s b
  Kind _ -> Kind s

instance Refine Type Type where
  apply (Substitutions ss) t@(TVar v s) = withSpan s (Map.findWithDefault t v ss)
  apply ss (a :-> b) = apply ss a :-> apply ss b
  apply ss (TTup tys) = TTup $ apply ss <$> tys
  apply ss (TList tx) = TList $ apply ss tx
  apply _ t@TData {} = t
  apply _ t@TRef {} = t
  apply _ t@TInt {} = t
  apply _ t@Kind {} = t

instance Unify Type where
  unifyingSubstitutions t t' | withSpan emptySpan t == withSpan emptySpan t' = return $ Substitutions Map.empty
  unifyingSubstitutions (TTup txs) (TTup tys) = unifyMany txs tys
  unifyingSubstitutions (TList tx) (TList ty) = unifyingSubstitutions tx ty
  unifyingSubstitutions (TVar v _) t = v `bind` t
  unifyingSubstitutions t (TVar v _) = v `bind` t
  unifyingSubstitutions (t1 :-> t2) (t3 :-> t4) = unifyMany [t1, t2] [t3, t4]
  unifyingSubstitutions t1@TRef {} t2@TData {} = unifyingSubstitutions t2 t1
  unifyingSubstitutions (TData n _ _) (TRef n' _) | n == n' = return $ Substitutions Map.empty
  unifyingSubstitutions t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv _) = v == tv
  isVar _ _ = False

instance Template Type where
  freeTypeVars = \case
    TInt _ -> Set.empty
    TTup tys -> foldr (Set.union . freeTypeVars) Set.empty tys
    TList tx -> freeTypeVars tx
    TData _ _ _ -> Set.empty
    TRef _ _ -> Set.empty
    a :-> b -> freeTypeVars a `Set.union` freeTypeVars b
    TVar v _ -> Set.singleton v
    Kind _ -> Set.empty

  instantiate ty = do
    let vs = Set.toList $ freeTypeVars ty
    vs' <- forM vs $ const (fresh (spanOf ty))
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ case ty of
      TInt {} -> ty
      TTup tys -> TTup $ apply s <$> tys
      TList tx -> TList $ apply s tx
      TData n sp cs -> TData n sp $ (\(c, sp, ts) -> (c, sp, apply s <$> ts)) <$> cs
      TRef {} -> ty
      TVar {} -> ty
      a :-> b -> apply s a :-> apply s b
      Kind s -> Kind s
