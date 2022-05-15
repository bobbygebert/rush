{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Rush.Ast (Ast (..), Term (..), Constructor (..)) where

import Data.Text hiding (unwords)
import Rush.Expression
import Rush.Type

data Ast s = Ast {name :: Text, ty :: s, value :: Term s}
  deriving (Show, Eq, Foldable, Functor)

data Term s = Expr (Expr s) | Type (Text, s) [Constructor s]
  deriving (Eq, Foldable, Functor)

instance (Show s) => Show (Term s) where
  show = \case
    Expr e -> show e
    Type (n, _) c -> unpack n ++ " [ " ++ show c ++ " ]"

data Constructor s = Constructor Text s [Type]
  deriving (Eq, Foldable, Functor)

instance Show (Constructor s) where
  show (Constructor n _ ts) = unwords (unpack n : (("(" ++) . (++ ")") . show <$> ts))
