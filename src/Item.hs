{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Item (desugar, Item (..)) where

import Ast
import Control.Monad
import Data.Text hiding (foldr, zip)
import Expression
import qualified Pattern

data Item c = Item {name :: Text, ty :: c, value :: Expr c}
  deriving (Show, Eq, Foldable, Functor)

desugar :: Ast c -> Item c
desugar = \case
  Constant (n, c) e -> Item n c e
  Fn (n, c) ps b -> Item n c (desugarFnPat freshNames ps b)

desugarFnPat :: [Text] -> [Pattern.Pattern c] -> Expr c -> Expr c
desugarFnPat fresh ps b = close vars
  where
    close [] = Match (uncurry Var <$> vars) [ps] b
    close ((x, c) : vs) = Lambda (x, c) (close vs)
    vars = zip fresh cs
    cs = getC <$> ps
    getC = \case
      Pattern.Binding _ c' -> c'
      Pattern.Num _ c' -> c'

freshNames :: [Text]
freshNames = pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
