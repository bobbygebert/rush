{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Rush.Item where

import Data.Text
import Rush.Expression (Expr)

data Item t
  = Num Text t
  | Data Text t [Item t]
  | Lambda (Text, t) (Expr t)
  deriving (Show, Eq, Functor, Foldable)

data Named t = Named Text (Item t)
  deriving (Show, Eq, Functor, Foldable)

instance Traversable Item where
  traverse f (Num n ty) = Num n <$> f ty
  traverse f (Data c ty xs) = Data c <$> f ty <*> traverse (traverse f) xs
  traverse f (Lambda (x, tx) b) = Lambda . (x,) <$> f tx <*> traverse f b

instance Traversable Named where
  traverse f (Named n c) = Named n <$> traverse f c
