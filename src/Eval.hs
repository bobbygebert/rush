{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Eval (eval, spec, unConst, Constant (..), Named (..)) where

import Control.Monad (msum)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text hiding (foldr, foldr1, span)
import Debug.Trace
import Expression
import Infer (Context (Context, defs))
import Span
import Test.Hspec as Hspec
import Type hiding (spec)
import Prelude hiding (lookup, span)

data Constant t
  = CNum Text t
  | CData Text t [Constant t]
  | CLambda (Text, t) (Expr t)
  | CType (Text, t) (Text, t) [Type]
  deriving (Show, Eq, Functor, Foldable)

data Named t = Named Text (Constant t)
  deriving (Show, Eq, Functor, Foldable)

instance Traversable Constant where
  traverse f (CNum n ty) = CNum n <$> f ty
  traverse f (CData c ty xs) = CData c <$> f ty <*> traverse (traverse f) xs
  traverse f (CLambda (x, tx) b) = CLambda . (x,) <$> f tx <*> traverse f b
  traverse f (CType (n, k) (c, t) ts) =
    CType
      <$> ((n,) <$> f k)
      <*> ((c,) <$> f t)
      <*> pure ts

instance Traversable Named where
  traverse f (Named n c) = Named n <$> traverse f c

eval :: Context (Constant Type) -> Expr Type -> Constant Type
eval ctx e =
  let get = lookup ctx
      extend (x, c) = Context . Map.insert x c . Map.delete x . defs
      evalBinOp op a b = case (eval ctx a, eval ctx b) of
        (CNum a ty@TInt {}, CNum b TInt {}) ->
          let c = pack . show $ read (unpack a) `op` read (unpack b)
           in CNum c ty
        _ -> error "unreachable"
   in trace ("evaluating: " ++ show e) $ case e of
        Num n ty -> CNum n ty
        Var v ty -> get v
        Add a b -> evalBinOp (+) a b
        Sub a b -> evalBinOp (-) a b
        Mul a b -> evalBinOp (*) a b
        Div a b -> evalBinOp (/) a b
        Mod a b -> evalBinOp mod a b
        Tup {} -> error "todo"
        List {} -> error "todo"
        Cons {} -> error "todo"
        Match xs arms -> case msum $ uncurry (match ctx xs) <$> arms of
          Just c -> c
          Nothing -> error "non-exhaustive match"
        Lambda (x, tx) b -> CLambda (x, tx) b
        App ty f x -> case eval ctx f of
          CLambda (x', tx) b -> ty <$ with (x', eval ctx x) ctx eval b
          _ -> error "unreachable"
        Data c ty xs -> CData c ty (eval ctx <$> xs)

match :: Context (Constant Type) -> [Expr Type] -> [Expr Type] -> Expr Type -> Maybe (Constant Type)
match ctx [] [] b = Just $ eval ctx b
match ctx (x : xs) (p : ps) b =
  let x' = eval ctx x
   in case p of
        Var x'' _ -> with (x'', x') ctx match xs ps b
        Num n ty
          | eval ctx (Num n ty) `eq` x' -> match ctx xs ps b
          | otherwise -> Nothing
          where
            eq :: Constant Type -> Constant Type -> Bool
            eq (CNum a _) (CNum b _) = a == b
            eq _ _ = error "unreachable"
        Tup {} -> error "todo"
        List {} -> error "todo"
        Cons {} -> error "todo"
        Data {} -> error "todo"
        _ -> error "unreachable"
match _ _ _ _ = error "unreachable"

with :: (Text, c) -> Context c -> (Context c -> f) -> f
with (x, c) ctx f = f (extend (x, c) ctx)

extend :: (Text, c) -> Context c -> Context c
extend (x, c) = Context . Map.insert x c . Map.delete x . defs

unConst :: Constant Type -> Expr Type
unConst = \case
  CLambda x b -> Lambda x b
  CNum n ty -> Num n ty
  _ -> error "unreachable"

lookup :: Context (Constant Type) -> Text -> Constant Type
lookup ctx = fromMaybe (error $ show ctx) . flip Map.lookup (defs ctx)

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: SpecWith ()
spec = describe "Eval" $ do
  it "evaluates addition" $ do
    eval
      emptyContext
      (Add (Num "1" (TInt s0)) (Add (Num "2" (TInt s2)) (Num "3" (TInt s3))))
      `shouldBe` CNum "6" (TInt s0)

  it "evaluates application" $ do
    let ctx = [("f", CLambda ("x", TInt s0) (Add (Var "x" (TInt s1)) (Var "x" (TInt s2))))]
    eval
      (Context $ Map.fromList ctx)
      (App (TInt s0) (Var "f" (TInt s1 :-> TInt s2)) (Num "2" (TInt s3)))
      `shouldBe` CNum "4" (TInt s0)

  it "evaluates numeric match" $ do
    eval
      emptyContext
      (Match [Num "1" (TInt s0)] [([Num "1" (TInt s1)], Num "2" (TInt s2))])
      `shouldBe` CNum "2" (TInt s2)

  it "evaluates binding match" $ do
    eval
      emptyContext
      (Match [Num "2" (TInt s0)] [([Var "x" (TInt s1)], Var "x" (TInt s2))])
      `shouldBe` CNum "2" (TInt s0)

  it "evaluates multi parameter match" $ do
    eval
      emptyContext
      ( Match
          [Num "1" (TInt s0), Num "2" (TInt s1)]
          [([Num "1" (TInt s2), Var "x" (TInt s3)], Var "x" (TInt s4))]
      )
      `shouldBe` CNum "2" (TInt s1)

  it "evaluates multi branch match" $ do
    eval
      emptyContext
      ( Match
          [Num "2" (TInt s0)]
          [ ([Num "1" (TInt s1)], Num "1" (TInt s2)),
            ([Num "2" (TInt s3)], Num "3" (TInt s4))
          ]
      )
      `shouldBe` CNum "3" (TInt s4)

emptyContext = Context {defs = Map.empty}

s0 = span "mod" (8, 8) (8, 8)

s1 = span "mod" (1, 1) (1, 1)

s2 = span "mod" (2, 2) (2, 2)

s3 = span "mod" (3, 3) (3, 3)

s4 = span "mod" (4, 4) (4, 4)
