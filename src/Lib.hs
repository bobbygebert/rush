module Lib (build) where

import Data.Text
import Data.Text.Lazy (toStrict)
import Generate
import LLVM.Pretty (ppllvm)
import Parser
import System.FilePath

build :: FilePath -> Text -> Either Text Text
build path source =
  (toStrict . ppllvm)
    . buildModule (takeBaseName path)
    <$> parseModule path source
