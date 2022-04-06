{-# LANGUAGE DeriveFunctor #-}

module Item (Item (..), Expr (..)) where

import Data.Text
import Expression

data Item c = Constant (Text, c) (Expr c) c
  deriving (Show, Eq, Functor)
