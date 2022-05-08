{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Ast (Ast (..)) where

import Data.Text
import Expression

data Ast c
  = Constant (Text, c) (Expr c)
  | Fn (Text, c) [([Expr c], Expr c)]
  | Type (Text, c) (Text, c)
  deriving (Show, Eq, Foldable, Functor)
