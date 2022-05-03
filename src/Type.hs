{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Type (typeOf, typeOfP, spanOf, typeItem, Type (..), spec) where

import Ast
import Control.Monad
import Control.Monad.Except
import Data.List hiding (lookup)
import qualified Data.List as List hiding (lookup)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, null, zip)
import Debug.Trace
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
  | TTup [Type]
  | TVar Text Span
  | Type :-> Type
  deriving (Eq)

instance Show Type where
  show = \case
    TInt _ -> "Int"
    TTup xs -> "(" ++ intercalate ", " (show <$> xs) ++ ")"
    TVar txt _ -> unpack txt
    a :-> b -> "(" ++ show a ++ " -> " ++ show b ++ ")"

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

typeExpr :: Expr Span -> Infer Type (Expr Type)
typeExpr = \case
  Num n c -> pure $ Num n (TInt c)
  Tup xs -> Tup <$> mapM typeExpr xs
  Var v c -> Var v . withSpan c <$> lookup v
  Add a b -> do
    a' <- typeExpr a
    b' <- typeExpr b
    ensure $ typeOf a' :~ TInt emptySpan
    ensure $ typeOf a' :~ typeOf b'
    return $ Add a' b'
  -- TODO: unify tarms
  Match xs arms -> do
    xs' <- mapM typeExpr xs
    bs' <- mapM match arms
    let tps = fmap typeOfP . fst <$> bs'
    let txs = typeOf <$> xs'
    mapM_ (mapM_ (ensure . uncurry (:~))) (zip txs <$> tps)
    return $ Match xs' bs'
    where
      match (ps, b) = do
        ps' <- mapM typePattern ps
        b' <- with (bindings =<< ps') (typeExpr b)
        return (ps', b')
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
  Tup xs -> TTup $ typeOf <$> xs
  Var _ ty -> ty
  Add a _ -> typeOf a
  Match xs ((ps, b) : _) -> typeOf b
  Match _ _ -> error "unreachable"
  Lambda (_, tx) b -> tx :-> typeOf b
  App ty f x -> ty

typeOfP :: Pattern.Pattern Type -> Type
typeOfP = \case
  Pattern.Binding _ ty -> ty
  Pattern.Num _ ty -> ty
  Pattern.Tup pats -> TTup $ typeOfP <$> pats

bindings :: Pattern.Pattern Type -> [(Text, Type)]
bindings = \case
  Pattern.Binding x tx -> [(x, tx)]
  Pattern.Num _ _ -> []
  Pattern.Tup ps -> bindings =<< ps

typePattern :: Pattern.Pattern Span -> Infer Type (Pattern.Pattern Type)
typePattern = \case
  Pattern.Num n s -> pure $ Pattern.Num n (TInt s)
  Pattern.Binding b s -> Pattern.Binding b <$> fresh s
  Pattern.Tup ps -> Pattern.Tup <$> mapM typePattern ps

freshTypeVars :: [Span -> Type]
freshTypeVars = TVar . pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

-- TODO: Merge Spans
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TTup tys -> spanOf $ head tys
  TVar _ s -> s
  a :-> b -> spanOf a

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TTup tys -> TTup $ withSpan s <$> tys
  TVar v _ -> TVar v s
  a :-> b -> withSpan s a :-> withSpan s b

instance Refinable Type Type where
  apply (Substitutions ss) t@(TVar v s) = withSpan s (Map.findWithDefault t v ss)
  apply ss (a :-> b) = apply ss a :-> apply ss b
  apply ss (TTup tys) = TTup $ apply ss <$> tys
  apply _ t@TInt {} = t

instance Unifiable Type where
  unifyingSubstitutions t t' | withSpan emptySpan t == withSpan emptySpan t' = return $ Substitutions Map.empty
  unifyingSubstitutions (TTup txs) (TTup tys) = unifyMany txs tys
  unifyingSubstitutions (TVar v _) t = v `bind` t
  unifyingSubstitutions t (TVar v _) = v `bind` t
  unifyingSubstitutions (t1 :-> t2) (t3 :-> t4) = unifyMany [t1, t2] [t3, t4]
  unifyingSubstitutions t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

  isVar v (TVar tv _) = v == tv
  isVar _ _ = False

instance Template Type where
  freeTypeVars = \case
    TInt _ -> Set.empty
    TTup tys -> foldr (Set.union . freeTypeVars) Set.empty tys
    a :-> b -> freeTypeVars a `Set.union` freeTypeVars b
    TVar v _ -> Set.singleton v

  instantiate ty = do
    let vs = Set.toList $ freeTypeVars ty
    vs' <- forM vs $ const (fresh (spanOf ty))
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ case ty of
      TInt {} -> ty
      TTup tys -> TTup $ apply s <$> tys
      TVar {} -> ty
      a :-> b -> apply s a :-> apply s b

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

s5 = Parser.span (5, 5) (5, 5)

s6 = Parser.span (6, 6) (6, 6)

spec :: SpecWith ()
spec = describe "Type" $ do
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
      let i = Item "f" s0 (Match [Var "x" s1] [([Pattern.Num "1" s2], Num "2" s3)])
      let o =
            Item
              "f"
              (TInt s0)
              ( Match
                  [Var "x" (TInt s1)]
                  [([Pattern.Num "1" (TInt s2)], Num "2" (TInt s3))]
              )
      typeItem c i `shouldBe` Right o

    it "infers type of Tup" $ do
      let c = Context Map.empty
      let i = Item "f" s0 (Match [Tup [Num "1" s1]] [([Pattern.Tup [Pattern.Num "1" s2]], Num "2" s3)])
      let o =
            Item
              "f"
              (TInt s0)
              ( Match
                  [Tup [Num "1" (TInt s1)]]
                  [([Pattern.Tup [Pattern.Num "1" (TInt s2)]], Num "2" (TInt s3))]
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

    it "unifies Tup types" $ do
      let c = Context $ Map.fromList [("g", TTup [TInt s0, TInt s1] :-> TInt s2)]
      let i = Item "f" s0 (Lambda ("x", s1) (Lambda ("y", s2) (App s3 (Var "g" s4) (Tup [Var "x" s5, Var "y" s6]))))
      let o =
            Item
              "f"
              (TInt s0 :-> TInt s0 :-> TInt s0)
              ( Lambda
                  ("x", TInt s1)
                  ( Lambda
                      ("y", TInt s2)
                      ( App
                          (TInt s3)
                          (Var "g" (TTup [TInt s4, TInt s4] :-> TInt s4))
                          (Tup [Var "x" (TInt s5), Var "y" (TInt s6)])
                      )
                  )
              )
      typeItem c i `shouldBe` Right o
