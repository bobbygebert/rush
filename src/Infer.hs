{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Infer where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader hiding (local)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor
import Data.Default
import Data.Functor
import Data.List (intercalate, partition)
import qualified Data.Map as Map
import Data.Map.Ordered
import qualified Data.Map.Ordered as OMap
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, intercalate, partition, tail, unlines, zip)
import Debug.Trace
import Span

data Constraint t
  = (:~) t t
  deriving (Functor)

infix 1 :~

instance (Show t) => Show (Constraint t) where
  show (a :~ b) = show a ++ " ~ " ++ show b

type InferT s t c = WriterT [Constraint t] (ExceptT TypeError (ReaderT c (State s)))

type Infer t = InferT (FreshTypeVarStream t) t (Definitions t)

data Context t = Context {defs :: OMap Name t}
  deriving (Show)

extend :: Name -> t -> Context t -> Context t
extend n t c = c {defs = defs c >| (n, t)}

instance Default (Context t) where
  def = Context OMap.empty

data Definitions t = Definitions {local :: Context t, global :: Context t}
  deriving (Show)

type Solve = Except TypeError

newtype Substitutions t = Substitutions (Map.Map Name t)
  deriving (Eq, Show)

class Unify t where
  unifyingSubstitutions :: t -> t -> Solve (Substitutions t)
  match :: t -> [ts] -> Solve t
  match = error "Not implemented"
  isVar :: Name -> t -> Bool

class Refine a t where
  apply :: Substitutions t -> a -> a

class Template a where
  freeTypeVars :: a -> Set.Set Name
  instantiate ::
    (TypeVarStream m t, Refine a t) =>
    a ->
    InferT m t c a

runInferT :: s -> c -> InferT s t c a -> Either TypeError (a, [Constraint t])
runInferT state env =
  flip evalState state
    . flip runReaderT env
    . runExceptT
    . runWriterT

runInfer :: [Span -> t] -> Definitions t -> Infer t a -> Either TypeError (a, [Constraint t])
runInfer typeVars env =
  flip evalState typeVars
    . flip runReaderT env
    . runExceptT
    . runWriterT

solveConstraints :: (Eq t, Unify t, Refine t t, Show t) => [Constraint t] -> Either TypeError (Substitutions t)
solveConstraints constraints = runExcept substitutions
  where
    substitutions = solve (Substitutions Map.empty) constraints
    solve ss@(Substitutions ss') cs = trace (unlines $ (show <$> Map.toList ss') ++ (show <$> cs)) $ do
      let isVague (a :~ b) = (/=) <$> unifyingSubstitutions a b <*> unifyingSubstitutions b a
      (vague, strict) <-
        bimap (snd <$>) (snd <$>)
          . partition fst
          <$> (zip <$> mapM isVague cs <*> pure cs)
      case strict ++ vague of
        [] -> trace ("substitutions:\n" ++ unlines (show <$> Map.toList ss')) return ss
        (t :~ t') : cs' -> do
          ss' <- unifyingSubstitutions t t'
          solve (ss' `compose` ss) (apply ss' cs')

ensure :: Constraint t -> InferT s t c ()
ensure c = tell [c]

unifyMany :: (Unify t, Refine t t, Show t) => [t] -> [t] -> Solve (Substitutions t)
unifyMany [] [] = return $ Substitutions Map.empty
unifyMany (t : ts) (t' : ts') =
  do
    ss <- unifyingSubstitutions t t'
    ss' <- unifyMany (apply ss ts) (apply ss ts')
    return (ss' `compose` ss)
unifyMany t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

bind :: (Eq t, Unify t, Show t, Template t) => Name -> t -> Solve (Substitutions t)
bind v t
  | isVar v t = return $ Substitutions Map.empty
  | v `Set.member` freeTypeVars t = throwError $ pack $ "binding failed: " ++ show (v, t)
  | otherwise = return (Substitutions $ Map.singleton v t)

lookup ::
  (Show c, Show t, Refine t t, Unify t, Template t, TypeVarStream m t, Globals t c, Locals t c) =>
  Name ->
  InferT m t c t
lookup v = do
  env <- ask
  local <- asks (OMap.lookup v . defs . locals)
  global <- instantiate =<< asks (OMap.lookup v . defs . globals)
  case local <|> global of
    Just t -> pure t
    Nothing -> throwError . pack $ show v ++ " is undefined in: " ++ show env

type FreshTypeVarStream t = [Span -> t]

instance TypeVarStream (FreshTypeVarStream t) t where
  freshTypeVar span = do
    stream <- get
    put $ tail stream
    return $ head stream span

fresh :: (TypeVarStream s t) => Span -> InferT s t c t
fresh = freshTypeVar

class TypeVarStream s t where
  freshTypeVar :: Span -> InferT s t c t

class Globals t g where
  globals :: g -> Context t
  withGlobal :: [(Name, t)] -> InferT s t g a -> InferT s t g a

class Locals t l where
  locals :: l -> Context t
  with :: [(Name, t)] -> InferT s t l a -> InferT s t l a

instance Globals t (Definitions t) where
  globals = global
  withGlobal vs = Reader.local (extend vs)
    where
      extend vs c = c {global = Context $ foldr (flip (>|)) (defs $ global c) vs}

instance Locals t (Definitions t) where
  locals = local
  with vs = Reader.local (extend vs)
    where
      extend vs c = c {local = Context $ foldr (flip (>|)) (defs $ local c) vs}

instance (Functor f, Refine a t) => Refine (f a) t where
  apply ss = fmap (apply ss)

instance (Foldable a, Template t) => Template (a t) where
  freeTypeVars = foldr (Set.union . freeTypeVars) Set.empty
  instantiate a = do
    let vs = Set.toList $ freeTypeVars a
    vs' <- forM vs $ const (fresh emptySpan)
    let s = Substitutions $ Map.fromList $ zip vs vs'
    return $ apply s a

type Name = Text

type TypeError = Text

compose :: Refine t t => Substitutions t -> Substitutions t -> Substitutions t
(Substitutions ss') `compose` (Substitutions ss) =
  Substitutions $ Map.map (apply (Substitutions ss')) ss `Map.union` ss'
