{-# LANGUAGE LambdaCase #-}

module Rush.Desugar where

import Control.Monad
import Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import Data.Text hiding (foldr, head, unwords, zip)
import Rush.Ast
import Rush.Expression
import Rush.Parser (Parsed)
import qualified Rush.Parser as Parser
import Rush.Type
import Span

desugar :: Parsed Span -> Ast Span
desugar = \case
  Parser.Constant (n, s) e -> Ast n s (Expr e)
  Parser.Fn (n, s) arms -> Ast n s (Expr $ desugarFnArms arms)
  Parser.Type (n, s1) cs -> Ast n s1 (Type (n, s1) (desugar' . substituteSelf <$> cs))
    where
      desugar' (c, s2, ts) = Constructor c s2 ts
      substituteSelf (c, s, ts) = (c, s, substituteSelf' <$> ts)
      substituteSelf' ty@(TData n' s _)
        | n' == n = TRef n s
        | otherwise = ty
      substituteSelf' ty = ty

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
      Data _ c' _ -> c'
      _ -> error "todo: better error message"
desugarFnArms _ = error "unreachable"

constructors :: Ast Span -> [Ast Type]
constructors (Ast _ _ term) = case term of
  Expr {} -> []
  Type (ty, sty) cs -> constructor <$> cs
    where
      cs' = (\(Constructor c s ts) -> (c, s, ts)) <$> cs
      constructor (Constructor c sc ts) = Ast c cty . Expr $ case args of
        [] -> Data c dty args
        args -> desugarFnArms [(args, Data c dty args)]
        where
          cty = foldr (:->) dty ts
          dty = TData ty sc cs'
          args = uncurry Var <$> zip freshNames ts
          expr = Expr $ case args of
            [] -> Data c dty args
            args -> desugarFnArms [(args, Data c dty args)]

constructorTypes :: Ast Span -> OMap Text Type
constructorTypes (Ast _ _ term) = case term of
  Expr {} -> OMap.empty
  Type (ty, sty) cs -> OMap.fromList (constructorType <$> cs)
    where
      cs' = (\(Constructor c s ts) -> (c, s, ts)) <$> cs
      constructorType (Constructor c sc ts) =
        (c, foldr (:->) (TData ty sc cs') ts)

freshNames :: [Text]
freshNames = pack <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
