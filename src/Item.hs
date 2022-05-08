{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Item (desugar, Item (..)) where

import qualified Ast
import Control.Monad
import Data.Text hiding (foldr, head, zip)
import Expression

data Item s = Item {name :: Text, ty :: s, value :: Expr s}
  deriving (Show, Eq, Foldable, Functor)

desugar :: Ast.Ast s -> Item s
desugar = \case
  Ast.Constant (n, s) e -> Item n s e
  Ast.Fn (n, s) arms -> Item n s (desugarFnArms arms)
  Ast.Type (n, s1) (c, s2) -> Item n s1 (Type (c, s2) (c, s2))

desugarFnArms :: [([Expr c], Expr c)] -> Expr c
desugarFnArms (arm@(ps, _) : arms) = close args
  where
    close [] = Match (uncurry Var <$> args) (arm : arms)
    close ((x, c) : vs) = Lambda (x, c) (close vs)
    args = zip freshNames cs
    cs = getC <$> ps
    getC = \case
      Var _ c' -> c'
      Num _ c' -> c'
      Tup ps -> getC $ head ps
      List c' _ -> c'
      Cons h _ -> getC h
      Data (_, c') -> c'
      _ -> error "todo: better error message"
desugarFnArms _ = error "unreachable"

freshNames :: [Text]
freshNames = pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
