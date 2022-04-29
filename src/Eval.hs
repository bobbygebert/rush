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
import Test.Hspec as Hspec
import Type hiding (spec)
import Prelude hiding (lookup)

eval :: Context Constant -> Expr Type -> Constant
eval ctx =
  let get = lookup ctx
   in \case
        Num n ty -> Constant.Num n ty
        Var v ty -> get v
        Add a b -> case (eval ctx a, eval ctx b) of
          (Constant.Num a ty@TInt {}, Constant.Num b TInt {}) ->
            let c = pack . show $ read (unpack a) + read (unpack b)
             in Constant.Num c ty
          _ -> error "unreachable"
        Match ex pat ex' -> error "Const match not implemented"
        Lambda x b -> Constant.Lambda x b
        App ty ex ex' -> error "Const app not implemented"

lookup :: Context Constant -> Text -> Constant
lookup ctx = fromMaybe (error "unreachable") . flip Map.lookup (locals ctx)

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: IO ()
spec = hspec $ do
  it "evaluates addition" $ do
    eval
      emptyContext
      (Add (Num "1" (TInt s0)) (Add (Num "2" (TInt s2)) (Num "3" (TInt s3))))
      `shouldBe` Constant.Num "6" (TInt s0)

emptyContext = Context {locals = Map.empty}

s0 = Parser.span (8, 8) (8, 8)

s1 = Parser.span (1, 1) (1, 1)

s2 = Parser.span (2, 2) (2, 2)

s3 = Parser.span (3, 3) (3, 3)
