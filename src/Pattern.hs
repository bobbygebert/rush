{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Pattern (Pattern (..)) where

import Data.Text

data Pattern c
  = Binding Text c
  | Num Text c
  deriving (Show, Eq, Foldable, Functor)
