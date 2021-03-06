{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Rush.Eval (eval, spec, unItem) where

import Control.Monad (msum)
import qualified Data.Map as Map
import Data.Map.Ordered hiding (lookup)
import qualified Data.Map.Ordered as OMap
import Data.Maybe
import Data.Text hiding (foldr, foldr1, span)
import Debug.Trace
import Infer (Context (Context, defs))
import Rush.Expression
import Rush.Item (Item)
import qualified Rush.Item as Item
import Rush.Type hiding (spec)
import Span
import Test.Hspec as Hspec
import Prelude hiding (lookup, span)

eval :: Context (Item Type) -> Expr Type -> Item Type
eval ctx e =
  let get = lookup ctx
      extend (x, c) = Context . (>| (x, c)) . defs
      evalBinOp op a b = case (eval ctx a, eval ctx b) of
        (Item.Num a ty@TInt {}, Item.Num b TInt {}) ->
          let c = pack . show $ read (unpack a) `op` read (unpack b)
           in Item.Num c ty
        _ -> error "unreachable"
   in trace ("evaluating: " ++ show e) $ case e of
        Num n ty -> Item.Num n ty
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
        Lambda (x, tx) b -> Item.Lambda (x, tx) b
        App ty f x -> case eval ctx f of
          Item.Lambda (x', tx) b -> ty <$ with (x', eval ctx x) ctx eval b
          _ -> error "unreachable"
        Data c ty xs -> Item.Data c ty (eval ctx <$> xs)

match :: Context (Item Type) -> [Expr Type] -> [Expr Type] -> Expr Type -> Maybe (Item Type)
match ctx [] [] b = Just $ eval ctx b
match ctx (x : xs) (p : ps) b =
  let x' = eval ctx x
   in case p of
        Var x'' _ -> with (x'', x') ctx match xs ps b
        Num n ty
          | eval ctx (Num n ty) `eq` x' -> match ctx xs ps b
          | otherwise -> Nothing
          where
            eq :: Item Type -> Item Type -> Bool
            eq (Item.Num a _) (Item.Num b _) = a == b
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
extend (x, c) = Context . (>| (x, c)) . defs

unItem :: Item Type -> Expr Type
unItem = \case
  Item.Lambda x b -> Lambda x b
  Item.Num n ty -> Num n ty
  Item.Data c td xs -> Data c td (unItem <$> xs)

lookup :: Context (Item Type) -> Text -> Item Type
lookup ctx = fromMaybe (error $ show ctx) . flip OMap.lookup (defs ctx)

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
      `shouldBe` Item.Num "6" (TInt s0)

  it "evaluates application" $ do
    let ctx = [("f", Item.Lambda ("x", TInt s0) (Add (Var "x" (TInt s1)) (Var "x" (TInt s2))))]
    eval
      (Context $ OMap.fromList ctx)
      (App (TInt s0) (Var "f" (TInt s1 :-> TInt s2)) (Num "2" (TInt s3)))
      `shouldBe` Item.Num "4" (TInt s0)

  it "evaluates numeric match" $ do
    eval
      emptyContext
      (Match [Num "1" (TInt s0)] [([Num "1" (TInt s1)], Num "2" (TInt s2))])
      `shouldBe` Item.Num "2" (TInt s2)

  it "evaluates binding match" $ do
    eval
      emptyContext
      (Match [Num "2" (TInt s0)] [([Var "x" (TInt s1)], Var "x" (TInt s2))])
      `shouldBe` Item.Num "2" (TInt s0)

  it "evaluates multi parameter match" $ do
    eval
      emptyContext
      ( Match
          [Num "1" (TInt s0), Num "2" (TInt s1)]
          [([Num "1" (TInt s2), Var "x" (TInt s3)], Var "x" (TInt s4))]
      )
      `shouldBe` Item.Num "2" (TInt s1)

  it "evaluates multi branch match" $ do
    eval
      emptyContext
      ( Match
          [Num "2" (TInt s0)]
          [ ([Num "1" (TInt s1)], Num "1" (TInt s2)),
            ([Num "2" (TInt s3)], Num "3" (TInt s4))
          ]
      )
      `shouldBe` Item.Num "3" (TInt s4)

emptyContext = Context {defs = OMap.empty}

s0 = span "mod" (8, 8) (8, 8)

s1 = span "mod" (1, 1) (1, 1)

s2 = span "mod" (2, 2) (2, 2)

s3 = span "mod" (3, 3) (3, 3)

s4 = span "mod" (4, 4) (4, 4)
