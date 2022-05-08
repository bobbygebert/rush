{-# LANGUAGE OverloadedStrings #-}

module BuildTest where

import Data.Text hiding (unlines)
import qualified Lib
import System.IO.Temp
import System.Process
import Test.Hspec as Hspec

rush :: [String] -> IO FilePath
rush code = do
  ll <- writeSystemTempFile "Lib.ll" $ build $ unlines code
  bc <- emptySystemTempFile "Lib.bc"
  callProcess "llvm-as" [ll, "-o", bc]
  return bc

decl :: [String] -> IO String
decl decls =
  return $
    unlines $
      [ "#include <stdint.h>",
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "void panic(void) { abort(); }"
      ]
        ++ decls

evalInt :: FilePath -> String -> String -> IO String
evalInt = eval "%ld"

eval :: String -> FilePath -> String -> String -> IO String
eval fmt rush decls c = do
  c <-
    writeSystemTempFile "Main.c" $
      unlines
        [ decls,
          "int main(void) {",
          "    printf(\"" ++ fmt ++ "\", " ++ c ++ ");",
          "}"
        ]
  exec <- emptySystemTempFile "Main"
  callProcess "clang" [c, rush, "-Wno-override-module", "-o", exec]
  readProcess exec [] ""

build :: String -> String
build = unpack . unwrap . Lib.build "Lib.rush" . pack

unwrap :: Either [Text] ok -> ok
unwrap (Left err) = error $ unlines $ unpack <$> err
unwrap (Right ok) = ok

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: SpecWith ()
spec = describe "rush build" $ do
  it "builds source with module ID equal to module name" $ do
    let i = ""
    let o = "; ModuleID = 'Lib'"
    build i `shouldContain` o

  it "builds constants" $ do
    r <- rush ["x = 123"]
    d <- decl ["int64_t x;"]
    o <- evalInt r d "x"
    o `shouldBe` "123"

  it "builds constant expr" $ do
    r <- rush ["x = 1 + 2"]
    d <- decl ["int64_t x;"]
    o <- evalInt r d "x"
    o `shouldBe` "3"

  it "builds constant match expressions" $ do
    r <-
      rush
        [ "f 1 = 2",
          "f 2 = 3",
          "x = f 1"
        ]
    d <- decl ["int64_t x;"]
    o <- evalInt r d "x"
    o `shouldBe` "2"

  it "builds constant function application" $ do
    r <-
      rush
        [ "f x = x + x",
          "y = f 2"
        ]
    d <- decl ["int64_t y;"]
    o <- evalInt r d "y"
    o `shouldBe` "4"

  it "builds global references" $ do
    r <-
      rush
        [ "x = 123",
          "y = x"
        ]
    d <- decl ["int64_t y;"]
    o <- evalInt r d "y"
    o `shouldBe` "123"

  it "builds simple functions taking and returning Int" $ do
    r <- rush ["f x = x + 2"]
    d <- decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(1)"
    o `shouldBe` "3"

  it "builds functions with single Int equality pattern" $ do
    r <- rush ["f 1 = 2"]
    d <- decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(1)"
    o `shouldBe` "2"

  it "builds functions with multiple Int equality patterns" $ do
    r <- rush ["f 1 2 = 3"]
    d <-
      decl
        [ "struct a { int64_t a; };",
          "struct a f(int64_t);",
          "int64_t _cls_f(struct a*, int64_t);"
        ]
    o <- evalInt r d "({ struct a cls = f(1); _cls_f(&cls, 2);})"
    o `shouldBe` "3"

  it "builds functions with multiple Int equality branches" $ do
    r <-
      rush
        [ "f 1 = 2",
          "f 2 = 3"
        ]
    d <- decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(1) + f(2)"
    o `shouldBe` "5"

  it "builds functions with multiple Int parameters" $ do
    r <- rush ["f x y = x + y"]
    d <-
      decl
        [ "struct a { int64_t a; };",
          "struct a f(int64_t);",
          "int64_t _cls_f(struct a*, int64_t);"
        ]
    o <- evalInt r d "({ struct a cls = f(1); _cls_f(&cls, 2);})"
    o `shouldBe` "3"

  it "builds function calls" $ do
    r <-
      rush
        [ "g x y = x + y",
          "f x y = g x y"
        ]
    d <-
      decl
        [ "struct a { int64_t a; };",
          "struct a f(int64_t);",
          "int64_t _cls_f(struct a*, int64_t);"
        ]
    o <- evalInt r d "({ struct a cls = f(1); _cls_f(&cls, 2);})"
    o `shouldBe` "3"

  it "builds tuple functions" $ do
    r <- rush ["f (x, y) = x + y"]
    d <-
      decl
        [ "struct args { int64_t x; int64_t y; };",
          "int64_t f(struct args *);"
        ]
    o <- evalInt r d "f(&((struct args) { 1, 2 }))"
    o `shouldBe` "3"

  it "builds functions returning tuples" $ do
    r <-
      rush
        [ "h (x, y) = x + y",
          "g x = (x, x)",
          "f x = h (g x)"
        ]
    d <- decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(1)"
    o `shouldBe` "2"

  it "builds distinct monomorphic variants of functions" $ do
    r <-
      rush
        [ "h x = x",
          "add (x, y) = x + y",
          "g x = add (h (x + x, x + x))",
          "f x = h (x + x)"
        ]
    d <-
      decl
        [ "struct pair { int64_t a; int64_t b; };",
          "struct pair g(int64_t);",
          "int64_t f(int64_t);"
        ]
    o <- evalInt r d "f(1)"
    o `shouldBe` "2"

  it "builds lists" $ do
    r <-
      rush
        [ "list 2 = [1, 2]",
          "sum [x, y] = x + y",
          "f x = sum (list x)"
        ]
    d <-
      decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(2)"
    o `shouldBe` "3"

  it "builds cons" $ do
    r <-
      rush
        [ "list 3 = []",
          "list x = x :: list (x + 1)",
          "sum [] = 0",
          "sum (x :: xs) = x + (sum xs)",
          "f x = sum (list x)"
        ]
    d <-
      decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(0)"
    o `shouldBe` "3"

  it "builds closure sums" $ do
    r <-
      rush
        [ "suml [x, y] z = x + y + z",
          "sump (x, y) z = x + y + z",
          "h [g, f] = (g 1) + (f 2)",
          "i x = h [sump (x, x + 1), suml [x + 2, x + 3]]"
        ]
    d <-
      decl ["int64_t i(int64_t);"]
    o <- evalInt r d "i(1)"
    o `shouldBe` "13"
