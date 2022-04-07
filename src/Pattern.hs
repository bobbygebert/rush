{-# LANGUAGE DeriveFunctor #-}

module Pattern (Pattern (..)) where

import Data.Text

data Pattern c = Binding Text c
  deriving (Show, Eq, Functor)
