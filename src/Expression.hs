{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Expression (Expr (..)) where

import Data.List (intercalate)
import Data.Text hiding (intercalate, unwords)
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
  deriving (Eq, Foldable, Functor)

instance (Show t) => Show (Expr t) where
  show = \case
    Num n _ -> unpack n
    Tup xs -> "(" ++ intercalate ", " (show <$> xs) ++ ")"
    List _ xs -> "[" ++ intercalate ", " (show <$> xs) ++ "]"
    Var v ty -> "(" ++ unpack v ++ ": " ++ show ty ++ ")"
    Add a b -> "(" ++ show a ++ " + " ++ show b ++ ")"
    Match xs ps ->
      "(match " ++ unwords (("(" ++) . (++ ")") . show <$> xs) ++ " {"
        ++ intercalate ", " (showArm <$> ps)
        ++ "})"
      where
        showArm (ps, b) = unwords (("(" ++) . (++ ")") . show <$> ps) ++ " -> " ++ show b
    Lambda (x, tx) b -> "((" ++ unpack x ++ ": " ++ show tx ++ ") -> " ++ show b ++ ")"
    App ty f x -> "(" ++ show f ++ " " ++ show x ++ ": " ++ show ty ++ ")"

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
