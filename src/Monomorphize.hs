{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module Monomorphize where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor
import Data.Function
import Data.Functor
import Data.List hiding (init, lookup)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Text hiding (concatMap, filter, foldr, head, init, partition, reverse, tail, unlines, zip)
import qualified Data.Text.Internal.Fusion.Size as Map
import qualified Eval as Rush
import qualified Expression as Rush
import IR
import Infer
import Parser (Span, emptySpan)
import qualified Pattern
import qualified Type as Rush
import Prelude hiding (init, lookup)

ir :: [Rush.Named Rush.Type] -> [IR.Named Type]
ir = generate . solve . runBuild . (unpack <=< closeOver)
  where
    unpack = const $ gets $ reverse . definitions
    closeOver [] = return ()
    closeOver (c@(Rush.Named n e) : cs) = do
      ty <- closeOverConstant c
      with [(n, ty)] $ closeOver cs

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

type Generate = InferT (State GenerateState) Type

data GenerateState = GenerateState
  { generated :: Map.Map (Text, Type) (IR.Constant Type),
    templates :: Context (IR.Constant Type),
    numbers :: [Text]
  }
  deriving (Show)

instance TypeVarStream (State GenerateState) Type where
  freshTypeVar span = do
    state <- get
    let n : ns = numbers state
    put $ state {numbers = ns}
    return $ TVar n span

runGenerate :: Context Type -> Context (IR.Constant Type) -> Generate [IR.Named Type] -> [IR.Named Type]
runGenerate types templates =
  solve
    . either (error . show) id
    . flip evalState (GenerateState Map.empty templates (pack . show <$> [0 ..]))
    . flip runReaderT types
    . runExceptT
    . runWriterT
    . unpack
  where
    unpack as = do
      as' <- as
      gs <- gets $ Map.toList . generated
      let gs' = (\((name, _), c) -> IR.Named name c) <$> gs
      return $ gs' ++ as'

generate :: [IR.Named Type] -> [IR.Named Type]
generate cs =
  runGenerate
    (Context types)
    (Context templates)
    (mapM generate' targets)
  where
    generate' (IR.Named name c) =
      IR.Named name <$> case c of
        IR.CNum {} -> pure c
        IR.CFn tc (x, tx) b -> IR.CFn tc (x, tx) <$> monomorphize (Set.singleton x) b
    noLocals = Set.empty
    types = Map.fromList $ (\(IR.Named n c) -> (n, typeOf $ unConst c)) <$> cs
    (templates, targets) =
      first
        (Map.fromList . fmap (\(IR.Named n c) -> (n, c)))
        (templatesAndTargets cs)
    templatesAndTargets =
      partition
        ( (/= 0) . Set.size
            . foldr (Set.union . freeTypeVars) Set.empty
            . (\(IR.Named _ c) -> unConst c)
        )

monomorphize :: Set.Set Text -> Expr Type -> Generate (Expr Type)
monomorphize locals e = case e of
  Num {} -> pure e
  Unit -> pure e
  Tup xs -> Tup <$> mapM (monomorphize locals) xs
  Var v ty -> extract v ty locals e
  Add a b -> Add <$> monomorphize locals a <*> monomorphize locals b
  Match xs as -> Match <$> mapM (monomorphize locals) xs <*> mapM match as
    where
      match (ps, b) =
        let bs = foldr (Set.union . bindings) Set.empty ps
         in (ps,) <$> monomorphize (locals `Set.union` bs) b
  Fn tc (x, tx) b -> Fn tc (x, tx) <$> monomorphize (Set.insert x locals) b
  Closure name cs f -> Closure name cs <$> extract name (typeOf f) locals f
  App ty f x -> App ty <$> monomorphize locals f <*> monomorphize locals x

extract :: Text -> Type -> Set.Set Text -> Expr Type -> Generate (Expr Type)
extract name ty locals defaultExpr
  | name `Set.member` locals = pure defaultExpr
  | otherwise = do
    generic <- mapM instantiate =<< template name
    case generic of
      Nothing -> pure defaultExpr
      Just c -> do
        state <- get
        let mangled = "_" <> head (numbers state) <> "_" <> name
        let ty' = typeOf $ unConst c
        ensure $ ty' :~ ty
        put
          state
            { generated = Map.insert (mangled, ty) c (generated state),
              numbers = tail (numbers state)
            }
        pure $ Var mangled ty

solve :: (Unify t, Refine a t, Refine t t, Show t) => (a, [Constraint t]) -> a
solve (items, constraints) =
  (`apply` items) $
    either (error . show) id $
      solveConstraints constraints

template :: Text -> Generate (Maybe (IR.Constant Type))
template v = do
  Context templates <- gets templates
  return $ Map.lookup v templates

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

closeOverConstant :: Rush.Named Rush.Type -> Build Type
closeOverConstant (Rush.Named name c) = ty'
  where
    ty' = (typeOf <$>) . define name =<< c'
    ty = init (Rush.typeOf $ Rush.unConst c)
    c' = case c of
      Rush.CNum n ty -> IR.CNum n <$> init ty
      Rush.CLambda (x, tx) b -> do
        tf <- ty
        tx <- ty <&> (\case TFn _ tx' _ -> tx'; _ -> error "unreachable")
        b' <- with [(name, tf), (x, tx)] $ closeOverExpr name b
        return $ IR.CFn TUnit (x, tx) b'

closeOverExpr :: Text -> Rush.Expr Rush.Type -> Build (Expr Type)
closeOverExpr parent e = case e of
  Rush.Num n ty -> Num n <$> init ty
  Rush.Tup xs -> Tup <$> mapM (closeOverExpr parent) xs
  Rush.Var x ty -> Var x <$> lookup x
  Rush.Add a b -> Add <$> closeOverExpr parent a <*> closeOverExpr parent b
  Rush.Match xs as -> Match <$> mapM (closeOverExpr parent) xs <*> mapM match as
    where
      match (ps, b) = do
        ps' <- mapM closeOverPattern ps
        b' <- with (typedBindings =<< ps') (closeOverExpr parent b)
        return (ps', b')
      closeOverPattern = \case
        Pattern.Binding b ty -> Pattern.Binding b <$> init ty
        Pattern.Num n ty -> Pattern.Num n <$> init ty
        Pattern.Tup xs -> Pattern.Tup <$> mapM closeOverPattern xs
  Rush.Lambda (x, tx) b -> mdo
    let name = "_cls_" <> parent
    tx' <- init tx
    cs <- captures (Set.singleton x) b
    b' <- with ((x, tx') : Map.toList (Map.map typeOf cs)) $ closeOverExpr name b
    tc <-
      return $
        if Map.size cs == 0
          then TUnit
          else TStruct (Map.map typeOf cs)
    f <- define name $ IR.CFn tc (x, tx') b'
    ensure $ typeOf f :~ TFn tc tx' (typeOf b')
    return $ case tc of
      TUnit -> f
      _ -> Closure name cs f
  Rush.App ty f x -> do
    f' <- closeOverExpr parent f
    x' <- closeOverExpr parent x
    let (tx', ty') = case typeOf f' of
          TClosure _ _ (TFn _ tx tb) -> (tx, tb)
          TFn _ tx tb -> (tx, tb)
          ty' -> error $ show (ty, ty')
    ensure $ typeOf x' :~ tx'
    return $ App ty' f' x'

captures :: Set.Set Text -> Rush.Expr Rush.Type -> Build (Map.Map Text (Expr Type))
captures bound =
  let unionMany = foldr Map.union Map.empty
   in \case
        Rush.Lambda (x, tx) b ->
          Map.filterWithKey (curry $ (/= x) . fst) <$> captures (Set.singleton x) b
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

bindings :: Pattern.Pattern b -> Set.Set Text
bindings = Set.fromList . fmap fst . typedBindings

typedBindings :: Pattern.Pattern b -> [(Text, b)]
typedBindings = \case
  Pattern.Binding x tx -> [(x, tx)]
  Pattern.Num _ _ -> []
  Pattern.Tup ps -> typedBindings =<< ps

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

freshNames :: [Text]
freshNames = pack . ('#' :) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])
