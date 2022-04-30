{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Item (desugar, Item (..)) where

import Ast
import Control.Monad
import Data.Text hiding (foldr, head, zip)
import Expression
import qualified Pattern

data Item c = Item {name :: Text, ty :: c, value :: Expr c}
  deriving (Show, Eq, Foldable, Functor)

desugar :: Ast c -> Item c
desugar = \case
  Constant (n, c) e -> Item n c e
  Fn (n, c) arms -> Item n c (desugarFnArms arms)

desugarFnArms :: [([Pattern.Pattern c], Expr c)] -> Expr c
desugarFnArms (arm@(ps, _) : arms) = close args
  where
    close [] = Match (uncurry Var <$> args) (arm : arms)
    close ((x, c) : vs) = Lambda (x, c) (close vs)
    args = zip freshNames cs
    cs = getC <$> ps
    getC = \case
      Pattern.Binding _ c' -> c'
      Pattern.Num _ c' -> c'
      Pattern.Tup ps -> getC $ head ps
desugarFnArms _ = error "unreachable"

freshNames :: [Text]
freshNames = pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
