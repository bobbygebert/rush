{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Rush.Monomorphize where

import Control.Monad.Reader
import Control.Monad.State
import Data.Default
import qualified Data.Map.Ordered as OMap
import Data.Maybe (fromJust, isJust)
import qualified Data.Set as Set
import Data.Text
import Debug.Trace
import Infer
import Rush.Eval
import Rush.Expression
import Rush.Type
import Prelude hiding (lookup)

type Monomorphize = InferT MonomorphizeState Type (Definitions Type)

data MonomorphizeState = MonomorphizeState
  { definitions :: Context (Constant Type),
    templates :: Context (Constant Type),
    names :: [Text]
  }
  deriving (Show)

instance TypeVarStream MonomorphizeState Type where
  freshTypeVar span = do
    state <- get
    let n : ns = names state
    put $ state {names = ns}
    return $ TVar n span

monomorphize :: [Named Type] -> [Named Type]
monomorphize =
  either (error . show) id
    . solve
    . either (error . show) id
    . runInferT
      MonomorphizeState {definitions = def, templates = def, names = freshNames}
      (Definitions (Context OMap.empty) (Context OMap.empty))
    . monomorphize'
  where
    monomorphize' :: [Named Type] -> Monomorphize [Named Type]
    monomorphize' [] = gets ((uncurry Named <$>) . OMap.assocs . defs . definitions)
    monomorphize' ((Named name constant) : cs)
      | Set.size (freeTypeVars (unConst constant)) > 0 = trace ("templating: " ++ unpack name) $ do
        ty <- mkTemplate name constant
        with [(name, ty)] $ monomorphize' cs
      | otherwise = trace ("monomorphizing: " ++ unpack name) $ do
        ty <-
          define name
            =<< with [(name, typeOf $ unConst constant)] (monomorphizeConstant constant)
        with [(name, ty)] $ monomorphize' cs

monomorphizeConstant :: Constant Type -> Monomorphize (Constant Type)
monomorphizeConstant constant = case constant of
  CNum {} -> pure constant
  CData {} -> pure constant
  CLambda (x, tx) b -> CLambda (x, tx) <$> with [(x, tx)] (monomorphizeExpr b)

monomorphizeExpr :: Expr Type -> Monomorphize (Expr Type)
monomorphizeExpr e = case e of
  Num n tn -> pure $ Num n tn
  Var v tv ->
    lookup v >>= \implTy ->
      if Set.size (freeTypeVars implTy) > 0
        then instantiateTemplate v tv
        else pure $ Var v tv
  Add a b -> Add <$> monomorphizeExpr a <*> monomorphizeExpr b
  Sub a b -> Sub <$> monomorphizeExpr a <*> monomorphizeExpr b
  Mul a b -> Mul <$> monomorphizeExpr a <*> monomorphizeExpr b
  Div a b -> Div <$> monomorphizeExpr a <*> monomorphizeExpr b
  Mod a b -> Mod <$> monomorphizeExpr a <*> monomorphizeExpr b
  Tup xs -> Tup <$> mapM monomorphizeExpr xs
  List tx xs -> List tx <$> mapM monomorphizeExpr xs
  Cons x xs -> Cons <$> monomorphizeExpr x <*> monomorphizeExpr xs
  Data c td xs -> Data c td <$> mapM monomorphizeExpr xs
  Match xs as -> Match <$> mapM monomorphizeExpr xs <*> mapM monomorphizeArm as
    where
      monomorphizeArm (ps, b) =
        let bs = bindings =<< ps
         in (ps,) <$> with bs (monomorphizeExpr b)
      bindings = \case
        Var x tx -> [(x, tx)]
        Num _ _ -> []
        Tup ps -> bindings =<< ps
        List _ ps -> bindings =<< ps
        Cons h t -> bindings h ++ bindings t
        Data _ _ ps -> bindings =<< ps
        _ -> error "unreachable"
  Lambda (x, tx) b -> Lambda (x, tx) <$> with [(x, tx)] (monomorphizeExpr b)
  App ty f x -> App ty <$> monomorphizeExpr f <*> monomorphizeExpr x

instantiateTemplate :: Text -> Type -> Monomorphize (Expr Type)
instantiateTemplate name ty = do
  s <- get
  r <- ask
  let mangled = "_" <> pack (show ty) <> "_" <> name
  let run = either (error . show) id . (solve <=< runInferT s r)
  if isDefined mangled r
    then pure $ Var mangled ty
    else do
      let partialInstance = run $ do
            template <- instantiate $ fromJust $ OMap.lookup name $ defs $ templates s
            ensure $ typeOf (unConst template) :~ ty
            pure template
      define mangled =<< with [(mangled, ty)] (monomorphizeConstant partialInstance)
      pure $ Var mangled ty
  where
    isDefined name = isJust . tryLookup name
    tryLookup :: Text -> Definitions Type -> Maybe Type
    tryLookup name = OMap.lookup name . defs . locals

mkTemplate :: Name -> Constant Type -> Monomorphize Type
mkTemplate n c = state $ \s -> (typeOf $ unConst c, s {templates = extend n c (templates s)})

define :: Text -> Constant Type -> Monomorphize Type
define n c = state $ \s -> (typeOf $ unConst c, s {definitions = extend n c (definitions s)})

freshNames :: [Text]
freshNames = pack . show <$> [0 ..]

solve :: (Refine a Type) => (a, [Constraint Type]) -> Either TypeError a
solve (items, constraints) = (`apply` items) <$> solveConstraints constraints
