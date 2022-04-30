{-# LANGUAGE DeriveFunctor #-}

module Constant (Constant (..), Named (..)) where

import Data.Text
import Expression
import Type

data Constant t
  = Num Text t
  | Lambda (Text, t) (Expr t)
  deriving (Show, Eq, Functor)

data Named t = Named Text t (Constant t)
  deriving (Show, Eq, Functor)
