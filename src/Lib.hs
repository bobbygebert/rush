{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib (build) where

import Ast
import Control.Arrow hiding (first)
import Control.Monad
import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.Function
import Data.Functor
import qualified Data.Map as Map
import Data.Text hiding (unlines)
import Data.Text.Lazy (toStrict)
import Debug.Trace
import Eval
import qualified Expression
import Generate
import Infer (Context (Context, defs), TypeError)
import Item
import LLVM.Pretty (ppllvm)
import Monomorphize (ir)
import Parser (parseModule)
import Span
import System.FilePath
import Type

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
      (Item name ty term) : is -> case ty of
        Kind _ -> reduce' ctx' is
        _ -> Named name c : reduce' ctx' is
        where
          c = case term of
            Item.Expr e -> eval ctx e
            Item.Type (n, k) cs -> CType (n, k) cs'
              where
                cs' = (\(Item.Constructor c t ts) -> (c, t, ts)) <$> cs
          ctx' = Context (Map.insert name c (defs ctx))

inferAndCheck :: [Item Span] -> Either [Text] [Item Type]
inferAndCheck = collect . fmap (first (pack . show)) . inferAndCheck' primitives
  where
    inferAndCheck' :: Context Type -> [Item Span] -> [Either TypeError (Item Type)]
    inferAndCheck' _ [] = []
    inferAndCheck' context (item : items) = case typeItem context item of
      Right item' -> do
        let tys = Map.fromList $ case value item' of
              Item.Expr e -> trace ("defining: " ++ show (name item', ty item', value item')) [(name item', ty item')]
              Item.Type (n, k) cs -> trace ("defining: " ++ unpack n ++ "\n" ++ unlines (show <$> cs)) []
        let context' =
              Context $
                Map.union (trace (unlines $ ("definining: " ++) . show <$> Map.toList (constructorTypes item)) constructorTypes item) $
                  Map.union tys (defs context)
        (Right <$> item' : constructors item) ++ inferAndCheck' context' items
      err -> trace ("error: " ++ show err) err : inferAndCheck' context items

primitives = Context {defs = Map.fromList [("Int", Kind emptySpan)]}

emptyContext = Context {defs = Map.empty}

parse :: String -> Text -> Either [Text] [Ast Span]
parse path source = first (: []) (parseModule path source)

collect :: [Either err ok] -> Either [err] [ok]
collect =
  partitionEithers
    >>> \case
      (err : errs, _) -> Left (err : errs)
      (_, oks) -> Right oks
