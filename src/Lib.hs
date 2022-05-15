{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib (build) where

import Control.Arrow hiding (first)
import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.Map.Ordered
import qualified Data.Map.Ordered as OMap
import Data.Text hiding (filter, unlines)
import Data.Text.Lazy (toStrict)
import Debug.Trace
import Generate
import Infer (Context (Context, defs), TypeError)
import LLVM.Pretty (ppllvm)
import Monomorphize (ir)
import Rush.Ast
import qualified Rush.Ast as Ast
import Rush.Desugar
import Rush.Eval
import Rush.Infer
import Rush.Monomorphize (monomorphize)
import Rush.Parser (Parsed, parseModule)
import Rush.Type
import Span
import System.FilePath

build :: FilePath -> Text -> Either [Text] Text
build path source =
  toStrict
    . ppllvm
    . buildModule (takeBaseName path)
    . ir
    . monomorphize
    . reduce
    <$> (inferAndCheck . (desugar <$>) =<< parse path source)

reduce :: [Ast Type] -> [Named Type]
reduce = reduce' emptyContext . (namedExprs =<<)
  where
    reduce' ctx = \case
      [] -> []
      (name, expr) : is -> Named name expr' : reduce' ctx' is
        where
          expr' = eval ctx expr
          ctx' = Context (defs ctx >| (name, expr'))
    namedExprs (Ast name _ (Ast.Expr expr)) = [(name, expr)]
    namedExprs (Ast _ _ Ast.Type {}) = []

inferAndCheck :: [Ast Span] -> Either [Text] [Ast Type]
inferAndCheck = collect . fmap (first (pack . show)) . inferAndCheck' primitives
  where
    inferAndCheck' :: Context Type -> [Ast Span] -> [Either TypeError (Ast Type)]
    inferAndCheck' _ [] = []
    inferAndCheck' context (item : items) = case typeAst context item of
      Right item' -> do
        let tys = OMap.fromList $ case value item' of
              Ast.Expr e -> trace ("defining: " ++ show (name item', ty item', value item')) [(name item', ty item')]
              Ast.Type (n, k) cs -> trace ("defining: " ++ unpack n ++ "\n" ++ unlines (show <$> cs)) []
        let context' =
              Context $
                constructorTypes item |<> tys |<> defs context
        (Right <$> item' : constructors item) ++ inferAndCheck' context' items
      err -> trace ("error: " ++ show err) err : inferAndCheck' context items

primitives = Context {defs = OMap.fromList [("Int", Kind emptySpan)]}

emptyContext = Context {defs = OMap.empty}

parse :: String -> Text -> Either [Text] [Parsed Span]
parse path source = first (: []) (parseModule path source)

collect :: [Either err ok] -> Either [err] [ok]
collect =
  partitionEithers
    >>> \case
      (err : errs, _) -> Left (err : errs)
      (_, oks) -> Right oks
