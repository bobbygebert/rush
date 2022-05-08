{-# LANGUAGE LambdaCase #-}

module Lib (build) where

import Ast
import Control.Arrow hiding (first)
import Control.Monad
import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.Function
import Data.Functor
import qualified Data.Map as Map
import Data.Text
import Data.Text.Lazy (toStrict)
import Debug.Trace
import Eval
import qualified Expression
import Generate
import Infer (Context (Context, defs), TypeError)
import Item
import LLVM.Pretty (ppllvm)
import Monomorphize (ir)
import Parser (Span, parseModule)
import System.FilePath
import Type
import Prelude hiding (unlines)

build :: FilePath -> Text -> Either [Text] Text
build path source =
  toStrict
    . ppllvm
    . buildModule (takeBaseName path)
    . ir
    . reduce
    <$> (inferAndCheck . (desugar <$>) =<< parse path source)

reduce :: [Item Type] -> [Named Type]
reduce = reduce' emptyContext
  where
    reduce' :: Context (Constant Type) -> [Item Type] -> [Named Type]
    reduce' ctx = \case
      [] -> []
      (Item name ty value) : is -> Named name c : reduce' ctx' is
        where
          c = eval ctx value
          ctx' = Context (Map.insert name c (defs ctx))

inferAndCheck :: [Item Span] -> Either [Text] [Item Type]
inferAndCheck = collect . fmap (first (pack . show)) . inferAndCheck' emptyContext
  where
    inferAndCheck' :: Context Type -> [Item Span] -> [Either TypeError (Item Type)]
    inferAndCheck' _ [] = []
    inferAndCheck' context (item : items) = case typeItem context item of
      Right item' -> do
        let (name', ty') = case value item' of
              Expression.Type (n, k) (c, ty) -> (c, ty)
              _ -> (name item', ty item')
        let context' = Context (Map.insert name' ty' (defs context))
        Right item' : inferAndCheck' context' items
      err -> err : inferAndCheck' context items

emptyContext = Context {defs = Map.empty}

parse :: String -> Text -> Either [Text] [Ast Span]
parse path source = first (: []) (parseModule path source)

collect :: [Either err ok] -> Either [err] [ok]
collect =
  partitionEithers
    >>> \case
      (err : errs, _) -> Left (err : errs)
      (_, oks) -> Right oks
