{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Monomorphize where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Function
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (filter, foldr, head, init, reverse, tail, unlines, zip)
import qualified Data.Text.Internal.Fusion.Size as Map
import Eval
import qualified Expression as Rush
import IR
import Infer
import Parser (Span, emptySpan)
import qualified Pattern
import qualified Type as Rush
import Prelude hiding (init, lookup)

type Build = InferT (State BuildState) Type

data BuildState = BuildState {definitions :: [IR.Named Type], names :: [Text], constraints :: [Constraint Type]}

instance TypeVarStream (State BuildState) Type where
  freshTypeVar span = do
    state <- get
    let n : ns = names state
    put $ state {names = ns}
    return $ TVar n span

runBuild :: Build a -> (a, [Constraint Type])
runBuild =
  either (error . show) id
    . flip evalState (BuildState [] freshNames [])
    . flip runReaderT (Context Map.empty)
    . runExceptT
    . runWriterT

freshNames :: [Text]
freshNames = pack . ('#' :) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

ir :: [Eval.Named Rush.Type] -> [IR.Named Type]
ir = either (error . show) id . monomorphize . solve . runBuild . (unpack <=< closeOver)
  where
    solve (items, constraints) = (\substitutions -> apply substitutions <$> items) <$> solveConstraints constraints
    monomorphize = fmap $ filter ((== 0) . Set.size . freeTypeVars . (\(IR.Named _ e) -> typeOf $ unConst e))
    unpack = const $ gets $ reverse . definitions
    closeOver [] = return ()
    closeOver (c@(Eval.Named n _) : cs) = do
      ty <- closeOverConstant c
      with [(n, ty)] $ closeOver cs

-- TODO: merge spans?
init :: Rush.Type -> Build Type
init = \case
  Rush.TInt s -> pure $ TInt s
  Rush.TTup tys -> TTup <$> mapM init tys
  Rush.TVar v s -> pure $ TVar v s
  a Rush.:-> b -> do
    ta <- init a
    tb <- init b
    tc <- freshVar (spanOf ta)
    TFn tc <$> init a <*> init b

closeOverConstant :: Eval.Named Rush.Type -> Build Type
closeOverConstant (Eval.Named name c) =
  (typeOf <$>) . define name =<< case c of
    Eval.CNum n ty -> IR.CNum n <$> init ty
    Eval.CLambda (x, tx) b -> do
      tx' <- init tx
      tb' <- freshVar (spanOf tx')
      let ty' = TFn TUnit tx' tb'
      b' <- with [(name, ty'), (x, tx')] $ closeOverExpr name b
      ensure $ tb' :~ typeOf b'
      return $ IR.CFn TUnit (x, tx') b'

closeOverExpr :: Text -> Rush.Expr Rush.Type -> Build (Expr Type)
closeOverExpr parent e = case e of
  Rush.Num n ty -> Num n <$> init ty
  Rush.Tup xs -> Tup <$> mapM (closeOverExpr parent) xs
  Rush.Var x _ -> Var x <$> lookup x
  Rush.Add a b -> Add <$> closeOverExpr parent a <*> closeOverExpr parent b
  Rush.Match xs as -> Match <$> mapM (closeOverExpr parent) xs <*> mapM match as
    where
      match (ps, b) = do
        ps' <- mapM closeOverPattern ps
        b' <- with (bindings =<< ps') (closeOverExpr parent b)
        return (ps', b')
      closeOverPattern = \case
        Pattern.Binding b ty -> Pattern.Binding b <$> init ty
        Pattern.Num n ty -> Pattern.Num n <$> init ty
        Pattern.Tup xs -> Pattern.Tup <$> mapM closeOverPattern xs
      bindings = \case
        Pattern.Binding x tx -> [(x, tx)]
        Pattern.Num _ _ -> []
        Pattern.Tup ps -> bindings =<< ps
  Rush.Lambda (x, tx) b -> mdo
    let name = "_cls_" <> parent
    tx' <- init tx
    b' <- with [(x, tx')] $ closeOverExpr name b
    let tb = typeOf b'
    cs <- captures (Set.singleton x) b
    tc <-
      return $
        if Map.size cs == 0
          then TUnit
          else TClosure name (Map.map typeOf cs) tb
    f <- define name $ IR.CFn tc (x, tx') b'
    return $ case tc of
      TUnit -> f
      _ -> Closure name cs f
  Rush.App ty f x -> do
    f' <- closeOverExpr parent f
    x' <- closeOverExpr parent x
    let ty' = case typeOf f' of
          TClosure _ _ (TFn _ _ tb) -> tb
          TFn _ _ tb -> tb
          ty' -> error $ show (ty, ty')
    return $ App ty' f' x'

captures :: Set.Set Text -> Rush.Expr Rush.Type -> Build (Map.Map Text (Expr Type))
captures bound =
  let unionMany = foldr Map.union Map.empty
   in \case
        Rush.Lambda (x, tx) b -> Map.filterWithKey (curry $ (/= x) . fst) <$> captures (Set.singleton x) b
        Rush.App _ f x -> Map.union <$> captures bound f <*> captures bound x
        Rush.Var x (_ Rush.:-> _) -> return Map.empty
        Rush.Var x tx -> do
          if x `Set.member` bound
            then return Map.empty
            else Map.singleton x . Var x <$> init tx
        Rush.Num {} -> return Map.empty
        Rush.Add a b -> Map.union <$> captures bound a <*> captures bound b
        Rush.Tup xs -> unionMany <$> mapM (captures bound) xs
        Rush.Match xs ps -> Map.union <$> bxs <*> bps
          where
            bxs = unionMany <$> mapM (captures bound) xs
            bps = unionMany <$> mapM (\(ps, es) -> excludeBindings ps <$> captures bound es) ps
            excludeBindings ps =
              Map.filterWithKey
                (curry $ not . (`Set.member` foldr (Set.union . bindings) Set.empty ps) . fst)
            bindings = \case
              Pattern.Binding b _ -> Set.singleton b
              _ -> Set.empty

freshName :: Build Text
freshName = do
  state <- get
  put state {names = tail $ names state}
  return $ head $ names state

freshVar :: Span -> Build Type
freshVar s = flip TVar s <$> freshName

define :: Text -> IR.Constant Type -> Build (Expr Type)
define name val = do
  state <- get
  put state {definitions = IR.Named name val : definitions state}
  return $ Var name (typeOf $ unConst val)
