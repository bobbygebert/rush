{-# LANGUAGE DeriveFunctor #-}

module Expression (Expr (..)) where

import Data.Text

data Expr c
  = Num Text c
  | Var Text c
  deriving (Show, Eq, Functor)
