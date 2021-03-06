{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Rush.Infer (typeAst, spec) where

import Control.Monad
import Data.Functor
import qualified Data.Map as Map
import Data.Map.Ordered hiding (lookup)
import qualified Data.Map.Ordered as OMap
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, span, unlines, unwords, zip)
import Debug.Trace
import Infer hiding (Type)
import qualified Infer
import Rush.Ast
import qualified Rush.Ast as Ast
import Rush.Expression hiding (Type)
import Rush.Type
import Span
import Test.Hspec (SpecWith, describe, it, shouldBe)
import Prelude hiding (lookup, span)

typeAst :: Context Type -> Ast Span -> Either TypeError (Ast Type)
typeAst context (Ast n s i) =
  let infer = runInfer freshTypeVars Definitions {local = Context OMap.empty, global = context}
      solve (ast, cs) = trace ("solving: " ++ show ast ++ "\n" ++ unlines (show <$> cs)) flip apply ast <$> solveConstraints cs
      normalize ast@(Ast _ ty _) = trace ("solved: " ++ show (apply (Substitutions ss) ast)) apply (Substitutions ss) ast
        where
          tvs = Set.toList (freeTypeVars ty)
          ss = Map.fromList $ zip tvs (freshTypeVars <*> repeat (spanOf ty))
   in (\x -> trace ("typed: " ++ show x) x) . (normalize <$>) . solve <=< infer $ do
        case i of
          Expr e -> do
            ty <- fresh s
            e' <- with [(n, ty)] $ typeExpr e
            ensure (ty :~ typeOf e')
            return . Ast n ty . Expr $ e'
          Type (t, s2) cs -> do
            let ty = TData n s2 (cs <&> (\(Constructor c s3 ts) -> (c, s3, ts)))
            let cs' = cs <&> (\(Constructor c _ ts) -> Constructor c ty ts)
            return $ Ast n (Kind s1) (Type (t, Kind s1) cs')

typeExpr :: Expr Span -> Infer Type (Expr Type)
typeExpr e = case e of
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
  Data c s xs -> do
    tc <- lookup c
    ty' <- withSpan s . rt <$> lookup c
    Data c ty' <$> mapM typeExpr xs
    where
      rt (a :-> b) = rt b
      rt ty = ty
  -- TODO: unify tarms
  Match xs arms -> do
    xs' <- mapM typeExpr xs
    bs' <- mapM match arms
    let tps = fmap typeOf . fst <$> bs'
    let txs = typeOf <$> xs'
    mapM_ (mapM_ (ensure . uncurry (:~))) (trace (show (zip txs <$> tps, bs')) (zip txs <$> tps))
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

typeBinOp op a b = op <$> constrained a (:~ TInt emptySpan) <*> constrained b (:~ TInt emptySpan)

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
  Data c s xs -> do
    tc' <- lookup c
    xs' <- mapM typePattern xs
    mapM_ (ensure . uncurry (:~)) (zip (typeOf <$> xs') (txs tc'))
    pure $ Data c (rt tc') xs'
    where
      txs (a :-> b) = a : txs b
      txs ty = []
      rt (a :-> b) = rt b
      rt ty = ty
  _ -> error "unreachable"

freshTypeVars :: [Span -> Type]
freshTypeVars = TVar . pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

constrained :: Expr Span -> (Type -> Constraint Type) -> Infer Type (Expr Type)
constrained e c = do
  e' <- typeExpr e
  ensure $ c (typeOf e')
  pure e'

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

s0 = span "mod" (8, 8) (8, 8)

s1 = span "mod" (1, 1) (1, 1)

s2 = span "mod" (2, 2) (2, 2)

s3 = span "mod" (3, 3) (3, 3)

s4 = span "mod" (4, 4) (4, 4)

s5 = span "mod" (5, 5) (5, 5)

s6 = span "mod" (6, 6) (6, 6)

spec :: SpecWith ()
spec = describe "Type" $ do
  describe "typeAst" $ do
    it "infers type of Num to be TInt" $ do
      let c = Context OMap.empty
      let i = Ast "n" s0 (Expr $ Num "1" s1)
      let o = Ast "n" (TInt s0) (Expr $ Num "1" (TInt s1))
      typeAst c i `shouldBe` Right o

    it "infers type of Var from Context" $ do
      let c = Context $ OMap.fromList [("v", TInt s1)]
      let i = Ast "n" s0 (Expr $ Var "v" s1)
      let o = Ast "n" (TInt s0) (Expr $ Var "v" (TInt s1))
      typeAst c i `shouldBe` Right o

    it "infers type of Add Expression" $ do
      let c = Context OMap.empty
      let i = Ast "n" s0 (Expr $ Add (Num "1" s1) (Num "2" s2))
      let o = Ast "n" (TInt s0) (Expr $ Add (Num "1" (TInt s1)) (Num "2" (TInt s2)))
      typeAst c i `shouldBe` Right o

    it "infers type of Lambda Expression" $ do
      let c = Context OMap.empty
      let i = Ast "f" s0 (Expr $ Lambda ("x", s1) (Num "2" s2))
      let o =
            Ast
              "f"
              (TVar "a" s0 :-> TInt s0)
              ( Expr $
                  Lambda
                    ("x", TVar "a" s1)
                    (Num "2" (TInt s2))
              )
      typeAst c i `shouldBe` Right o

    it "infers type of Match Expression" $ do
      let c = Context $ OMap.fromList [("x", TInt s4)]
      let i = Ast "f" s0 (Expr $ Match [Var "x" s1] [([Num "1" s2], Num "2" s3)])
      let o =
            Ast
              "f"
              (TInt s0)
              ( Expr $
                  Match
                    [Var "x" (TInt s1)]
                    [([Num "1" (TInt s2)], Num "2" (TInt s3))]
              )
      typeAst c i `shouldBe` Right o

    it "infers type of Tup" $ do
      let c = Context OMap.empty
      let i =
            Ast
              "f"
              s0
              ( Expr $
                  Match [Tup [Num "1" s1]] [([Tup [Num "1" s2]], Num "2" s3)]
              )
      let o =
            Ast
              "f"
              (TInt s0)
              ( Expr $
                  Match
                    [Tup [Num "1" (TInt s1)]]
                    [([Tup [Num "1" (TInt s2)]], Num "2" (TInt s3))]
              )
      typeAst c i `shouldBe` Right o

    it "infers type of App Expression" $ do
      let c = Context OMap.empty
      let i =
            Ast
              "f"
              s0
              ( Expr $
                  Lambda ("g", s1) (App s2 (Var "g" s3) (Num "123" s4))
              )
      let o =
            Ast
              "f"
              ((TInt s0 :-> TVar "a" s0) :-> TVar "a" s0)
              ( Expr $
                  Lambda
                    ("g", TInt s1 :-> TVar "a" s1)
                    ( App
                        (TVar "a" s2)
                        (Var "g" (TInt s3 :-> TVar "a" s3))
                        (Num "123" (TInt s4))
                    )
              )
      typeAst c i `shouldBe` Right o

    it "unifies Tup types" $ do
      let c = Context $ OMap.fromList [("g", TTup [TInt s0, TInt s1] :-> TInt s2)]
      let i =
            Ast
              "f"
              s0
              ( Expr $
                  Lambda ("x", s1) (Lambda ("y", s2) (App s3 (Var "g" s4) (Tup [Var "x" s5, Var "y" s6])))
              )
      let o =
            Ast
              "f"
              (TInt s0 :-> TInt s0 :-> TInt s0)
              ( Expr $
                  Lambda
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
      typeAst c i `shouldBe` Right o
