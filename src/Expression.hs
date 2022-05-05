{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Expression (Expr (..)) where

import Data.Text
import qualified Pattern

data Expr c
  = Num Text c
  | Tup [Expr c]
  | List c [Expr c]
  | Var Text c
  | Add (Expr c) (Expr c)
  | Match [Expr c] [([Pattern.Pattern c], Expr c)]
  | Lambda (Text, c) (Expr c)
  | App c (Expr c) (Expr c)
  deriving (Show, Eq, Foldable, Functor)

instance Traversable Expr where
  traverse f (Num n c) = Num n <$> f c
  traverse f (Tup xs) = Tup <$> traverse (traverse f) xs
  traverse f (List c xs) = List <$> f c <*> traverse (traverse f) xs
  traverse f (Var v c) = Var v <$> f c
  traverse f (Add a b) = Add <$> traverse f a <*> traverse f b
  traverse f (Match x b) =
    Match
      <$> traverse (traverse f) x
      <*> traverse (\(ps, b) -> (,) <$> traverse (traverse f) ps <*> traverse f b) b
  traverse f (Lambda (x, c) b) = Lambda . (x,) <$> f c <*> traverse f b
  traverse f (App c a b) = App <$> f c <*> traverse f a <*> traverse f b
