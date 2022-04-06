{-# LANGUAGE OverloadedStrings #-}

module BuildTest where

import Data.Text
import Lib
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
    (unpack . unwrap) (build "Lib.rush" i) `shouldContain` o
  it "builds constants" $ do
    let i = "x = 123"
    let o = "@x =    global i64 123"
    (unpack . unwrap) (build "Lib.rush" i) `shouldContain` o

unwrap :: (Show err) => Either err ok -> ok
unwrap (Left err) = error $ show err
unwrap (Right ok) = ok
