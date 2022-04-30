{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Expression (Expr (..)) where

import Data.Text
import qualified Pattern

data Expr c
  = Num Text c
  | Tup [Expr c]
  | Var Text c
  | Add (Expr c) (Expr c)
  | Match [Expr c] [([Pattern.Pattern c], Expr c)]
  | Lambda (Text, c) (Expr c)
  | App c (Expr c) (Expr c)
  deriving (Show, Eq, Foldable, Functor)
