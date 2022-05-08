{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Expression (Expr (..)) where

import Data.List (intercalate)
import Data.Text hiding (foldr, intercalate, unwords)

data Expr c
  = Num Text c
  | Var Text c
  | Add (Expr c) (Expr c)
  | Sub (Expr c) (Expr c)
  | Mul (Expr c) (Expr c)
  | Div (Expr c) (Expr c)
  | Mod (Expr c) (Expr c)
  | Tup [Expr c]
  | List c [Expr c]
  | Cons (Expr c) (Expr c)
  | Data (Text, c)
  | Match [Expr c] [([Expr c], Expr c)]
  | Lambda (Text, c) (Expr c)
  | App c (Expr c) (Expr c)
  | Type (Text, c) (Text, c)
  deriving (Eq, Foldable, Functor)

instance (Show t) => Show (Expr t) where
  show = \case
    Num n _ -> unpack n
    Var v ty -> "(" ++ unpack v ++ ": " ++ show ty ++ ")"
    Add a b -> showBinOp "+" a b
    Sub a b -> showBinOp "-" a b
    Mul a b -> showBinOp "*" a b
    Div a b -> showBinOp "/" a b
    Mod a b -> showBinOp "%" a b
    Tup xs -> "(" ++ intercalate ", " (show <$> xs) ++ ")"
    List _ xs -> "[" ++ intercalate ", " (show <$> xs) ++ "]"
    Cons h t -> "(" ++ foldr (\x -> (++ (" :: " ++ show x))) (show h) (nodes t) ++ ")"
      where
        nodes (Cons x xs) = x : nodes xs
        nodes x = [x]
    Data (c, ty) -> show c
    Match xs ps ->
      "(match " ++ unwords (("(" ++) . (++ ")") . show <$> xs) ++ " {"
        ++ intercalate ", " (showArm <$> ps)
        ++ "})"
      where
        showArm (ps, b) = unwords (("(" ++) . (++ ")") . show <$> ps) ++ " -> " ++ show b
    Lambda (x, tx) b -> "((" ++ unpack x ++ ": " ++ show tx ++ ") -> " ++ show b ++ ")"
    App ty f x -> "(" ++ show f ++ " " ++ show x ++ ": " ++ show ty ++ ")"
    Type (n, _) _ -> unpack n

showBinOp op a b = "(" ++ show a ++ " " ++ op ++ " " ++ show b ++ ")"

instance Traversable Expr where
  traverse f (Num n c) = Num n <$> f c
  traverse f (Var v c) = Var v <$> f c
  traverse f (Add a b) = traverseBinOp f Add a b
  traverse f (Sub a b) = traverseBinOp f Sub a b
  traverse f (Mul a b) = traverseBinOp f Mul a b
  traverse f (Div a b) = traverseBinOp f Div a b
  traverse f (Mod a b) = traverseBinOp f Mod a b
  traverse f (Tup xs) = Tup <$> traverse (traverse f) xs
  traverse f (List c xs) = List <$> f c <*> traverse (traverse f) xs
  traverse f (Cons h t) = Cons <$> traverse f h <*> traverse f t
  traverse f (Data (n, c)) = Data . (n,) <$> f c
  traverse f (Match x b) =
    Match
      <$> traverse (traverse f) x
      <*> traverse (\(ps, b) -> (,) <$> traverse (traverse f) ps <*> traverse f b) b
  traverse f (Lambda (x, c) b) = Lambda . (x,) <$> f c <*> traverse f b
  traverse f (App c a b) = App <$> f c <*> traverse f a <*> traverse f b
  traverse f (Type (n, a) (c, b)) = Type <$> ((n,) <$> f a) <*> ((c,) <$> f b)

traverseBinOp f op a b = op <$> traverse f a <*> traverse f b
