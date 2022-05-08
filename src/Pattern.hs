{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

module Pattern (Pattern (..)) where

import Data.Text

data Pattern c
  = Binding Text c
  | Num Text c
  | Tup [Pattern c]
  | List c [Pattern c]
  | Cons (Pattern c) (Pattern c)
  | Data (Text, c)
  deriving (Show, Eq, Foldable, Functor)

instance Traversable Pattern where
  traverse f (Binding x c) = Binding x <$> f c
  traverse f (Num n c) = Num n <$> f c
  traverse f (Tup ps) = Tup <$> traverse (traverse f) ps
  traverse f (List c ps) = List <$> f c <*> traverse (traverse f) ps
  traverse f (Cons h t) = Cons <$> traverse f h <*> traverse f t
  traverse f (Data (t, c)) = Data . (t,) <$> f c
