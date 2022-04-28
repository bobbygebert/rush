{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Item (desugar, Item (..)) where

import Ast
import Control.Monad
import Data.Text
import Expression
import qualified Pattern

data Item c = Item {name :: Text, ty :: c, value :: Expr c}
  deriving (Show, Eq, Foldable, Functor)

desugar :: Ast c -> Item c
desugar = \case
  Constant (n, c) e -> Item n c e
  Fn (n, c) p b -> Item n c (desugarFnPat freshNames p b)

desugarFnPat :: [Text] -> Pattern.Pattern c -> Expr c -> Expr c
desugarFnPat (x : xs) p b = Lambda (x, c) (Match (Var x c) p b)
  where
    c = case p of
      Pattern.Binding _ c' -> c'
      Pattern.Num _ c' -> c'
desugarFnPat _ _ _ = error "unreachable"

freshNames :: [Text]
freshNames = pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
