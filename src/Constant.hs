{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Constant (Constant (..), Named (..)) where

import Data.Text
import Expression (Expr)
import Type

data Constant t
  = Num Text t
  | Lambda (Text, t) (Expr t)
  deriving (Show, Eq, Functor, Foldable)

data Named t = Named Text t (Constant t)
  deriving (Show, Eq, Functor, Foldable)

instance Traversable Constant where
  traverse f (Num n ty) = Num n <$> f ty
  traverse f (Lambda (x, tx) b) = Lambda . (x,) <$> f tx <*> traverse f b

instance Traversable Named where
  traverse f (Named n t c) = Named n <$> f t <*> traverse f c
