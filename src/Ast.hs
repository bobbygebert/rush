{-# LANGUAGE DeriveFunctor #-}

module Ast (Ast (..)) where

import Data.Text
import Expression
import Pattern

data Ast c
  = Constant (Text, c) (Expr c)
  | Fn (Text, c) (Pattern c) (Expr c)
  deriving (Show, Eq, Functor)
