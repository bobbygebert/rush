{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Type (typeItem, Type (..), spec) where

import Ast
import Control.Monad
import Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (zip)
import Expression
import GHC.RTS.Flags (ProfFlags (descrSelector))
import Infer hiding (Type)
import qualified Infer
import Item
import Parser (Span, emptySpan, span)
import qualified Pattern
import Test.Hspec
import Prelude hiding (lookup)

data Type
  = TInt Span
  | TVar Text Span
  | Type :-> Type
  deriving (Show, Eq)

infixr 9 :->

typeItem :: Context Type -> Item Span -> Either TypeError (Item Type)
typeItem context (Item n s e) = normalize <$> (solve =<< infer)
  where
    infer = runInfer freshTypeVars context $ do
      ty <- fresh s
      e' <- with [(n, ty)] $ typeExpr e
      ensure (ty :~ typeOf e')
      return $ Item n ty e'
    solve (item, cs) = flip apply item <$> solveConstraints cs
    normalize item@(Item _ ty _) = apply (Substitutions ss) item
      where
        tvs = Set.toList (freeTypeVars item)
        ss = Map.fromList $ zip tvs (freshTypeVars <*> repeat (spanOf ty))

-- TODO: merge spans.
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TVar _ s -> s
  a :-> b -> spanOf a

typeExpr :: Expr Span -> Infer Type (Expr Type)
typeExpr = \case
  Num n c -> pure $ Num n (TInt c)
  Var v c -> Var v . withSpan c <$> lookup v
  Add a b -> Add <$> typeExpr a <*> typeExpr b
  Match x p b -> do
    x' <- typeExpr x
    p' <- typePattern p
    b' <- with (bindings p') (typeExpr b)
    return $ Match x' p' b'
  Lambda (x, s) b -> do
    tx <- fresh s
    Lambda (x, tx) <$> with [(x, tx)] (typeExpr b)
  App s f x -> do
    f' <- typeExpr f
    x' <- typeExpr x
    ty <- fresh s
    ensure (typeOf f' :~ typeOf x' :-> ty)
    App ty <$> typeExpr f <*> typeExpr x

typeOf :: Expr Type -> Type
typeOf = \case
  Num _ ty -> ty
  Var _ ty -> ty
  Add a _ -> typeOf a
  Match x _ b -> typeOf x :-> typeOf b
  Lambda (_, tx) b -> tx :-> typeOf b
  App ty f x -> ty

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TVar v _ -> TVar v s
  a :-> b -> withSpan s a :-> withSpan s b

bindings :: Pattern.Pattern Type -> [(Text, Type)]
bindings = \case
  Pattern.Binding x tx -> [(x, tx)]
  Pattern.Num _ _ -> []

typePattern :: Pattern.Pattern Span -> Infer Type (Pattern.Pattern Type)
typePattern = \case
  Pattern.Num n s -> pure $ Pattern.Num n (TInt s)
  Pattern.Binding b s -> Pattern.Binding b <$> fresh s

freshTypeVars :: [Span -> Type]
freshTypeVars = TVar . pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

instance Refinable Type Type where
  apply (Substitutions ss) t@(TVar v s) = withSpan s $ replace' t (Map.findWithDefault t v ss)
    where
      replace' t t' | withSpan emptySpan t == withSpan emptySpan t' = t
      replace' _ t'@(TVar v' s) = replace' t' (Map.findWithDefault t' v' ss)
      replace' _ t' = apply (Substitutions ss) t'
  apply ss (a :-> b) = apply ss a :-> apply ss b
  apply _ t@TInt {} = t

instance Unifiable Type where
  unifyingSubstitutions t t' | t == t' = return $ Substitutions Map.empty
  unifyingSubstitutions (TVar v _) t = v `bind` t
  unifyingSubstitutions t (TVar v _) = v `bind` t
  unifyingSubstitutions (t1 :-> t2) (t3 :-> t4) = unifyMany [t1, t2] [t3, t4]
  unifyingSubstitutions t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv _) = v == tv
  isVar _ _ = False

instance Template Type where
  freeTypeVars = \case
    TInt _ -> Set.empty
    a :-> b -> freeTypeVars a `Set.union` freeTypeVars b
    TVar v _ -> Set.singleton v

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

s0 = Parser.span (8, 8) (8, 8)

s1 = Parser.span (1, 1) (1, 1)

s2 = Parser.span (2, 2) (2, 2)

s3 = Parser.span (3, 3) (3, 3)

s4 = Parser.span (4, 4) (4, 4)

spec :: IO ()
spec = hspec $ do
  describe "typeItem" $ do
    it "infers type of Num to be TInt" $ do
      let c = Context Map.empty
      let i = Item "n" s0 (Num "1" s1)
      let o = Item "n" (TInt s0) (Num "1" (TInt s1))
      typeItem c i `shouldBe` Right o

    it "infers type of Var from Context" $ do
      let c = Context $ Map.fromList [("v", TInt s1)]
      let i = Item "n" s0 (Var "v" s1)
      let o = Item "n" (TInt s0) (Var "v" (TInt s1))
      typeItem c i `shouldBe` Right o

    it "infers type of Add Expression" $ do
      let c = Context Map.empty
      let i = Item "n" s0 (Add (Num "1" s1) (Num "2" s2))
      let o = Item "n" (TInt s0) (Add (Num "1" (TInt s1)) (Num "2" (TInt s2)))
      typeItem c i `shouldBe` Right o

    it "infers type of Lambda Expression" $ do
      let c = Context Map.empty
      let i = Item "f" s0 (Lambda ("x", s1) (Num "2" s2))
      let o =
            Item
              "f"
              (TVar "a" s0 :-> TInt s0)
              ( Lambda
                  ("x", TVar "a" s1)
                  (Num "2" (TInt s2))
              )
      typeItem c i `shouldBe` Right o

    it "infers type of Match Expression" $ do
      let c = Context $ Map.fromList [("x", TInt s4)]
      let i = Item "f" s0 (Match (Var "x" s1) (Pattern.Num "1" s2) (Num "2" s3))
      let o =
            Item
              "f"
              (TInt s0 :-> TInt s0)
              ( Match
                  (Var "x" (TInt s1))
                  (Pattern.Num "1" (TInt s2))
                  (Num "2" (TInt s3))
              )
      typeItem c i `shouldBe` Right o

    it "infers type of App Expression" $ do
      let c = Context Map.empty
      let i = Item "f" s0 (Lambda ("g", s1) (App s2 (Var "g" s3) (Num "123" s4)))
      let o =
            Item
              "f"
              ((TInt s0 :-> TVar "a" s0) :-> TVar "a" s0)
              ( Lambda
                  ("g", TInt s1 :-> TVar "a" s1)
                  ( App
                      (TVar "a" s2)
                      (Var "g" (TInt s3 :-> TVar "a" s3))
                      (Num "123" (TInt s4))
                  )
              )
      typeItem c i `shouldBe` Right o
