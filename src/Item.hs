{-# LANGUAGE DeriveFunctor #-}

module Item (Item (..)) where

import Data.Text
import Expression
import Pattern

data Item c
  = Constant (Text, c) (Expr c)
  | Fn (Text, c) (Pattern c) (Expr c)
  deriving (Show, Eq, Functor)
