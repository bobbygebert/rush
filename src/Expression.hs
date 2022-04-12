{-# LANGUAGE DeriveFunctor #-}

module Expression (Expr (..)) where

import Data.Text
import qualified Pattern

data Expr c
  = Num Text c
  | Var Text c
  | Add (Expr c) (Expr c)
  | Match (Text, c) (Pattern.Pattern c) (Expr c)
  | Lambda (Text, c) (Expr c)
  deriving (Show, Eq, Functor)
