{-# LANGUAGE LambdaCase #-}

module Lib (build) where

import Ast
import Constant (Constant, Named (Named))
import Control.Arrow hiding (first)
import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.Function
import Data.Functor
import qualified Data.Map as Map
import Data.Text
import Data.Text.Lazy (toStrict)
import Eval
import Generate
import Infer (Context (Context, locals), TypeError)
import Item
import LLVM.Pretty (ppllvm)
import Parser
import System.FilePath
import Type
import Prelude hiding (unlines)

build :: FilePath -> Text -> Either [Text] Text
build path source =
  toStrict
    . ppllvm
    . buildModule (takeBaseName path)
    . reduce
    <$> (inferAndCheck . fmap desugar =<< parse path source)

reduce :: [Item Type] -> [Named]
reduce = reduce' emptyContext
  where
    reduce' :: Context (Constant Type) -> [Item Type] -> [Named]
    reduce' ctx = \case
      [] -> []
      (Item name _ value) : is -> Named name c : reduce' ctx' is
        where
          c = eval ctx value
          ctx' = Context (Map.insert name c (locals ctx))

inferAndCheck :: [Item Span] -> Either [Text] [Item Type]
inferAndCheck = collect . fmap (first (pack . show)) . inferAndCheck' emptyContext
  where
    inferAndCheck' :: Context Type -> [Item Span] -> [Either TypeError (Item Type)]
    inferAndCheck' _ [] = []
    inferAndCheck' context (item : items) = case typeItem context item of
      Right item' ->
        let context' = Context (Map.insert (name item) (ty item') (locals context))
         in Right item' : inferAndCheck' context' items
      err -> err : inferAndCheck' context items

emptyContext = Context {locals = Map.empty}

parse :: String -> Text -> Either [Text] [Ast Span]
parse path source = first (: []) (parseModule path source)

collect :: [Either err ok] -> Either [err] [ok]
collect =
  partitionEithers
    >>> \case
      (err : errs, _) -> Left (err : errs)
      (_, oks) -> Right oks
