{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Eval (eval, spec, Constant (..), Named (..)) where

import Control.Monad (msum)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text hiding (foldr, foldr1)
import Expression
import Infer (Context (Context, locals))
import Parser (Span, emptySpan, span)
import qualified Pattern
import Test.Hspec as Hspec
import Type hiding (spec)
import Prelude hiding (lookup)

data Constant t
  = CNum Text t
  | CLambda (Text, t) (Expr t)
  deriving (Show, Eq, Functor, Foldable)

data Named t = Named Text (Constant t)
  deriving (Show, Eq, Functor, Foldable)

instance Traversable Constant where
  traverse f (CNum n ty) = CNum n <$> f ty
  traverse f (CLambda (x, tx) b) = CLambda . (x,) <$> f tx <*> traverse f b

instance Traversable Named where
  traverse f (Named n c) = Named n <$> traverse f c

eval :: Context (Constant Type) -> Expr Type -> Constant Type
eval ctx =
  let get = lookup ctx
      extend (x, c) = Context . Map.insert x c . Map.delete x . locals
   in \case
        Num n ty -> CNum n ty
        Tup {} -> error "todo"
        Var v ty -> get v
        Add a b -> case (eval ctx a, eval ctx b) of
          (CNum a ty@TInt {}, CNum b TInt {}) ->
            let c = pack . show $ read (unpack a) + read (unpack b)
             in CNum c ty
          _ -> error "unreachable"
        Match xs arms -> case msum $ uncurry (match ctx xs) <$> arms of
          Just c -> c
          Nothing -> error "non-exhaustive match"
        Lambda (x, tx) b -> CLambda (x, tx) b
        App ty f x -> case eval ctx f of
          CLambda (x', tx) b -> ty <$ with (x', eval ctx x) ctx eval b
          _ -> error "unreachable"

match ::
  Context (Constant Type) ->
  [Expr Type] ->
  [Pattern.Pattern Type] ->
  Expr Type ->
  Maybe (Constant Type)
match ctx [] [] b = Just $ eval ctx b
match ctx (x : xs) (p : ps) b =
  let x' = eval ctx x
   in case p of
        Pattern.Binding x'' _ -> with (x'', x') ctx match xs ps b
        Pattern.Num n ty
          | eval ctx (Num n ty) `eq` x' -> match ctx xs ps b
          | otherwise -> Nothing
          where
            eq :: Constant Type -> Constant Type -> Bool
            eq (CNum a _) (CNum b _) = a == b
            eq _ _ = error "unreachable"
        Pattern.Tup {} -> error "todo"
match _ _ _ _ = error "unreachable"

with :: (Text, c) -> Context c -> (Context c -> f) -> f
with (x, c) ctx f = f (extend (x, c) ctx)

extend :: (Text, c) -> Context c -> Context c
extend (x, c) = Context . Map.insert x c . Map.delete x . locals

unConst :: Constant Type -> Expr Type
unConst = \case
  CLambda x b -> Lambda x b
  CNum n ty -> Num n ty

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
      (Match [Num "1" (TInt s0)] [([Pattern.Num "1" (TInt s1)], Num "2" (TInt s2))])
      `shouldBe` CNum "2" (TInt s2)

  it "evaluates binding match" $ do
    eval
      emptyContext
      (Match [Num "2" (TInt s0)] [([Pattern.Binding "x" (TInt s1)], Var "x" (TInt s2))])
      `shouldBe` CNum "2" (TInt s0)

  it "evaluates multi parameter match" $ do
    eval
      emptyContext
      ( Match
          [Num "1" (TInt s0), Num "2" (TInt s1)]
          [([Pattern.Num "1" (TInt s2), Pattern.Binding "x" (TInt s3)], Var "x" (TInt s4))]
      )
      `shouldBe` CNum "2" (TInt s1)

  it "evaluates multi branch match" $ do
    eval
      emptyContext
      ( Match
          [Num "2" (TInt s0)]
          [ ([Pattern.Num "1" (TInt s1)], Num "1" (TInt s2)),
            ([Pattern.Num "2" (TInt s3)], Num "3" (TInt s4))
          ]
      )
      `shouldBe` CNum "3" (TInt s4)

emptyContext = Context {locals = Map.empty}

s0 = Parser.span (8, 8) (8, 8)

s1 = Parser.span (1, 1) (1, 1)

s2 = Parser.span (2, 2) (2, 2)

s3 = Parser.span (3, 3) (3, 3)

s4 = Parser.span (4, 4) (4, 4)
