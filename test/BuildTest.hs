{-# LANGUAGE OverloadedStrings #-}

module BuildTest where

import Data.Text hiding (unlines)
import qualified Lib
import Test.Hspec as Hspec

spec :: IO ()
spec = hspec $ do
  describe "rush build" buildSpec

-- TODO: Test generating .bc
buildSpec :: SpecWith ()
buildSpec = do
  it "builds source with module ID equal to module name" $ do
    let i = ""
    let o = "; ModuleID = 'Lib'"
    build i `shouldContain` o

  it "builds constants" $ do
    let i = "x = 123"
    let o = "@x =    global i64 123"
    build i `shouldContain` o

  it "builds constant expr" $ do
    let i = "x = 1 + 2"
    let o = "@x =    global i64 add i64 1, 2"
    build i `shouldContain` o

  it "builds global references" $ do
    let i = "x = 123\ny = x"
    let o = "@y =    global i64* @x"
    build i `shouldContain` o

  it "builds functions" $ do
    let i = "f x = x"
    let o =
          "define external ccc  i64 @f(i64  %a_0)    {\n"
            ++ "  ret i64 %a_0 \n"
            ++ "}"
    build i `shouldContain` o

  it "builds functions with patterns" $ do
    let i = "f 1 = 2"
    let o =
          "define external ccc  i64 @f(i64  %a_0)    {\n"
            ++ "; <label>:0:\n"
            ++ "  %1 = icmp eq i64 %a_0, 1 \n"
            ++ "  br i1 %1, label %continue_0, label %panic_0 \n"
            ++ "continue_0:\n"
            ++ "  br label %maybeContinue_0 \n"
            ++ "panic_0:\n"
            ++ "   call ccc  void  @panic()  \n"
            ++ "  br label %maybeContinue_0 \n"
            ++ "maybeContinue_0:\n"
            ++ "  %2 = phi i64 [2, %continue_0], [undef, %panic_0] \n"
            ++ "  ret i64 %2 \n"
            ++ "}"
    build i `shouldContain` o

  it "builds function calls" $ do
    let i =
          ""
            ++ "g x = x\n"
            ++ "f x = g x"
    let o =
          "define external ccc  i64 @f(i64  %a_0)    {\n"
            ++ "  %1 =  call ccc  i64  @g(i64  %a_0)  \n"
            ++ "  ret i64 %1 \n"
            ++ "}"
    build i `shouldContain` o

build :: String -> String
build = unpack . unwrap . Lib.build "Lib.rush" . pack

unwrap :: (Show err) => Either err ok -> ok
unwrap (Left err) = error $ show err
unwrap (Right ok) = ok
