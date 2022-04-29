{-# LANGUAGE OverloadedStrings #-}

module BuildTest where

import Data.Text hiding (unlines)
import qualified Lib
import System.IO.Temp
import System.Process
import Test.Hspec as Hspec

spec :: IO ()
spec = hspec $ do
  describe "rush build" buildSpec

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

unwrap :: (Show err) => Either err ok -> ok
unwrap (Left err) = error $ show err
unwrap (Right ok) = ok

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

buildSpec :: SpecWith ()
buildSpec = do
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

  it "builds function calls" $ do
    r <-
      rush
        [ "g x = x",
          "f x = g x"
        ]
    d <- decl ["int64_t f(int64_t);"]
    o <- evalInt r d "f(123)"
    o `shouldBe` "123"
