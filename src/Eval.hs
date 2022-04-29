{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Eval (eval, spec) where

import Constant (Constant)
import qualified Constant
import qualified Data.Map as Map
import Data.Maybe
import Data.Text
import Expression
import Infer (Context (Context, locals))
import Parser (Span, emptySpan, span)
import qualified Pattern
import Test.Hspec as Hspec
import Type hiding (spec)
import Prelude hiding (lookup)

eval :: Context (Constant Type) -> Expr Type -> Constant Type
eval ctx =
  let get = lookup ctx
      extend (x, c) = Context . Map.insert x c . Map.delete x . locals
   in \case
        Num n ty -> Constant.Num n ty
        Var v ty -> get v
        Add a b -> case (eval ctx a, eval ctx b) of
          (Constant.Num a ty@TInt {}, Constant.Num b TInt {}) ->
            let c = pack . show $ read (unpack a) + read (unpack b)
             in Constant.Num c ty
          _ -> error "unreachable"
        Match xs [ps] b -> match ctx xs ps b
        Lambda x b -> Constant.Lambda x b
        App ty f x -> case eval ctx f of
          Constant.Lambda (x', tx) b -> ty <$ with (x', eval ctx x) ctx eval b
          _ -> error "unreachable"
        _ -> error "unreachable"

match ::
  Context (Constant Type) ->
  [Expr Type] ->
  [Pattern.Pattern Type] ->
  Expr Type ->
  Constant Type
match ctx [] [] b = eval ctx b
match ctx (x : xs) (p : ps) b =
  let x' = eval ctx x
   in case p of
        Pattern.Binding x'' _ -> with (x'', x') ctx match xs ps b
        Pattern.Num n ty
          | eval ctx (Num n ty) `eq` x' -> match ctx xs ps b
          | otherwise -> error "non-exhaustive match"
          where
            eq :: Constant Type -> Constant Type -> Bool
            eq (Constant.Num a _) (Constant.Num b _) = a == b
            eq _ _ = error "unreachable"
match _ _ _ _ = error "unreachable"

with :: (Text, c) -> Context c -> (Context c -> f) -> f
with (x, c) ctx f = f (extend (x, c) ctx)

extend :: (Text, c) -> Context c -> Context c
extend (x, c) = Context . Map.insert x c . Map.delete x . locals

unConst :: Constant Type -> Expr Type
unConst = \case
  Constant.Lambda x b -> Lambda x b
  Constant.Num n ty -> Num n ty

lookup :: Context (Constant Type) -> Text -> Constant Type
lookup ctx = fromMaybe (error $ show ctx) . flip Map.lookup (locals ctx)

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
      `shouldBe` Constant.Num "6" (TInt s0)

  it "evaluates application" $ do
    let ctx = [("f", Constant.Lambda ("x", TInt s0) (Add (Var "x" (TInt s1)) (Var "x" (TInt s2))))]
    eval
      (Context $ Map.fromList ctx)
      (App (TInt s0) (Var "f" (TInt s1 :-> TInt s2)) (Num "2" (TInt s3)))
      `shouldBe` Constant.Num "4" (TInt s0)

  it "evaluates numeric match" $ do
    eval
      emptyContext
      (Match [Num "1" (TInt s0)] [[Pattern.Num "1" (TInt s1)]] (Num "2" (TInt s2)))
      `shouldBe` Constant.Num "2" (TInt s2)

  it "evaluates binding match" $ do
    eval
      emptyContext
      (Match [Num "2" (TInt s0)] [[Pattern.Binding "x" (TInt s1)]] (Var "x" (TInt s2)))
      `shouldBe` Constant.Num "2" (TInt s0)

  it "evaluates multi parameter match" $ do
    eval
      emptyContext
      ( Match
          [Num "1" (TInt s0), Num "2" (TInt s1)]
          [[Pattern.Num "1" (TInt s2), Pattern.Binding "x" (TInt s3)]]
          (Var "x" (TInt s4))
      )
      `shouldBe` Constant.Num "2" (TInt s1)

emptyContext = Context {locals = Map.empty}

s0 = Parser.span (8, 8) (8, 8)

s1 = Parser.span (1, 1) (1, 1)

s2 = Parser.span (2, 2) (2, 2)

s3 = Parser.span (3, 3) (3, 3)

s4 = Parser.span (4, 4) (4, 4)
