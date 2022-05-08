{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Type (bindings, typeOf, spanOf, typeItem, Type (..), spec) where

import Ast
import Control.Monad
import Control.Monad.Except
import Data.List hiding (lookup)
import qualified Data.List as List hiding (lookup)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, null, unlines, zip)
import Expression hiding (Type)
import qualified Expression
import GHC.RTS.Flags (ProfFlags (descrSelector))
import Infer hiding (Type)
import qualified Infer
import Item
import Parser (Span, emptySpan, span)
import Test.Hspec
import Prelude hiding (lookup)

data Type
  = TInt Span
  | TTup [Type]
  | TList Type
  | TVar Text Span
  | TData (Text, Span)
  | Type :-> Type
  | Kind Span
  deriving (Eq)

instance Show Type where
  show = \case
    TInt _ -> "Int"
    TTup xs -> "(" ++ intercalate ", " (show <$> xs) ++ ")"
    TList tx -> "[" ++ show tx ++ "]"
    TVar txt _ -> "'" ++ unpack txt
    TData (n, _) -> unpack n
    a :-> b -> show a ++ " -> " ++ show b
    Kind {} -> "*"

infixr 9 :->

typeItem :: Context Type -> Item Span -> Either TypeError (Item Type)
typeItem context (Item n s e) = normalize <$> (solve =<< infer)
  where
    infer = runInfer freshTypeVars Definitions {local = Context Map.empty, global = context} $ do
      ty <- fresh s
      e' <- with [(n, ty)] $ typeExpr e
      ensure (ty :~ typeOf e')
      return $ Item n ty e'
    solve (item, cs) = flip apply item <$> solveConstraints cs
    normalize item@(Item _ ty _) = apply (Substitutions ss) item
      where
        tvs = Set.toList (freeTypeVars ty)
        ss = Map.fromList $ zip tvs (freshTypeVars <*> repeat (spanOf ty))

typeExpr :: Expr Span -> Infer Type (Expr Type)
typeExpr = \case
  Num n c -> pure $ Num n (TInt c)
  Var v c -> Var v . withSpan c <$> lookup v
  Add a b -> typeBinOp Add a b
  Sub a b -> typeBinOp Sub a b
  Mul a b -> typeBinOp Mul a b
  Div a b -> typeBinOp Div a b
  Mod a b -> typeBinOp Mod a b
  Tup xs -> Tup <$> mapM typeExpr xs
  List c xs -> do
    ty <- fresh c
    List ty <$> mapM (`constrained` (ty :~)) xs
  Cons h t -> do
    h' <- typeExpr h
    Cons h' <$> constrained t (:~ TList (typeOf h'))
  Data (c, s) -> Data . (c,) . withSpan s <$> lookup c
  -- TODO: unify tarms
  Match xs arms -> do
    xs' <- mapM typeExpr xs
    bs' <- mapM match arms
    let tps = fmap typeOf . fst <$> bs'
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
    x' <- typeExpr x
    ty <- fresh s
    f' <- constrained f (:~ typeOf x' :-> ty)
    pure $ App ty f' x'
  Expression.Type (n, s1) (c, s2) -> pure $ Expression.Type (n, Kind s1) (c, TData (n, s2))

typeBinOp op a b = op <$> constrained a (:~ TInt emptySpan) <*> constrained b (:~ TInt emptySpan)

constrained :: Expr Span -> (Type -> Constraint Type) -> Infer Type (Expr Type)
constrained e c = do
  e' <- typeExpr e
  ensure $ c (typeOf e')
  pure e'

typeOf :: Expr Type -> Type
typeOf = \case
  Num _ ty -> ty
  Var _ ty -> ty
  Add a _ -> typeOf a
  Sub a _ -> typeOf a
  Mul a _ -> typeOf a
  Div a _ -> typeOf a
  Mod a _ -> typeOf a
  Tup xs -> TTup $ typeOf <$> xs
  List ty _ -> TList ty
  Cons h _ -> TList (typeOf h)
  Data (_, ty) -> ty
  Match xs ((ps, b) : _) -> typeOf b
  Match _ _ -> error "unreachable"
  Lambda (_, tx) b -> tx :-> typeOf b
  App ty f x -> ty
  Expression.Type (_, kind) _ -> kind

bindings :: Expr Type -> [(Text, Type)]
bindings = \case
  Var x tx -> [(x, tx)]
  Num _ _ -> []
  Tup ps -> bindings =<< ps
  List _ ps -> bindings =<< ps
  Cons h t -> bindings h ++ bindings t
  Data (_, _) -> []
  _ -> error "unreachable"

typePattern :: Expr Span -> Infer Type (Expr Type)
typePattern = \case
  Num n s -> pure $ Num n (TInt s)
  Var b s -> Var b <$> fresh s
  Tup ps -> Tup <$> mapM typePattern ps
  List s ps -> do
    ty <- fresh s
    ps' <- forM ps $ \p -> do
      p' <- typePattern p
      ensure $ ty :~ typeOf p'
      pure p'
    pure $ List ty ps'
  Cons h t -> Cons <$> typePattern h <*> typePattern t
  Data (c, s) -> Data . (c,) <$> lookup c
  _ -> error "unreachable"

freshTypeVars :: [Span -> Type]
freshTypeVars = TVar . pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

-- TODO: Merge Spans
spanOf :: Type -> Span
spanOf = \case
  TInt s -> s
  TTup tys -> spanOf $ head tys
  TList tx -> spanOf tx
  TVar _ s -> s
  TData (_, s) -> s
  a :-> b -> spanOf a
  Kind s -> s

withSpan :: Span -> Type -> Type
withSpan s = \case
  TInt _ -> TInt s
  TTup tys -> TTup $ withSpan s <$> tys
  TList tx -> TList $ withSpan s tx
  TVar v _ -> TVar v s
  TData (n, _) -> TData (n, s)
  a :-> b -> withSpan s a :-> withSpan s b
  Kind _ -> Kind s

instance Refine Type Type where
  apply (Substitutions ss) t@(TVar v s) = withSpan s (Map.findWithDefault t v ss)
  apply ss (a :-> b) = apply ss a :-> apply ss b
  apply ss (TTup tys) = TTup $ apply ss <$> tys
  apply ss (TList tx) = TList $ apply ss tx
  apply _ t@TData {} = t
  apply _ t@TInt {} = t
  apply _ t@Kind {} = t

instance Unify Type where
  unifyingSubstitutions t t' | withSpan emptySpan t == withSpan emptySpan t' = return $ Substitutions Map.empty
  unifyingSubstitutions (TTup txs) (TTup tys) = unifyMany txs tys
  unifyingSubstitutions (TList tx) (TList ty) = unifyingSubstitutions tx ty
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
    TList tx -> freeTypeVars tx
    TData (_, _) -> Set.empty
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
      TData (_, _) -> ty
      TVar {} -> ty
      a :-> b -> apply s a :-> apply s b
      Kind s -> Kind s

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
      let i = Item "f" s0 (Match [Var "x" s1] [([Num "1" s2], Num "2" s3)])
      let o =
            Item
              "f"
              (TInt s0)
              ( Match
                  [Var "x" (TInt s1)]
                  [([Num "1" (TInt s2)], Num "2" (TInt s3))]
              )
      typeItem c i `shouldBe` Right o

    it "infers type of Tup" $ do
      let c = Context Map.empty
      let i = Item "f" s0 (Match [Tup [Num "1" s1]] [([Tup [Num "1" s2]], Num "2" s3)])
      let o =
            Item
              "f"
              (TInt s0)
              ( Match
                  [Tup [Num "1" (TInt s1)]]
                  [([Tup [Num "1" (TInt s2)]], Num "2" (TInt s3))]
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
