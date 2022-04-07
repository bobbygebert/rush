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
  it "builds functions" $ do
    let i = "f x = x"
    let o =
          "define external ccc  i64 @f(i64  %x_0)    {\n"
            ++ "  ret i64 %x_0 \n"
            ++ "}"
    build i `shouldContain` o
  it "builds global references" $ do
    let i = "x = 123\ny = x"
    let o = "@y =    global i64* @x"
    build i `shouldContain` o

build :: Text -> String
build = unpack . unwrap . Lib.build "Lib.rush"

unwrap :: (Show err) => Either err ok -> ok
unwrap (Left err) = error $ show err
unwrap (Right ok) = ok
