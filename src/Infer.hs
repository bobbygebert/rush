{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Infer where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text hiding (foldr, head, tail, zip)
import Parser (Span)

type Name = Text

type TypeError = Text

data Constraint t = (:~) t t
  deriving (Show, Functor)

infix 1 :~

type InferT m t = WriterT [Constraint t] (ExceptT TypeError (ReaderT (Context t) m))

type Infer t = InferT (State (FreshTypeVarStream t)) t

type FreshTypeVarStream t = [Span -> t]

data Context t = Context {locals :: Map.Map Name t}
  deriving (Show)

type Solve = Except TypeError

newtype Substitutions t = Substitutions (Map.Map Name t)
  deriving (Show)

class Unifiable t where
  unifyingSubstitutions :: t -> t -> Solve (Substitutions t)
  isVar :: Name -> t -> Bool

class Refinable a t where
  apply :: Substitutions t -> a -> a

class Template a where
  freeTypeVars :: a -> Set.Set Name
  instantiate ::
    (MonadState [Span -> t] m, Refinable a t) =>
    a ->
    InferT m a a

runInfer :: [Span -> t] -> Context t -> Infer t a -> Either TypeError (a, [Constraint t])
runInfer typeVars env =
  flip evalState typeVars
    . flip runReaderT env
    . runExceptT
    . runWriterT

solveConstraints :: (Unifiable t, Refinable t t, Show t) => [Constraint t] -> Either TypeError (Substitutions t)
solveConstraints constraints = runExcept $ solve (Substitutions Map.empty) constraints
  where
    solve ss cs = case cs of
      [] -> return ss
      (t :~ t') : cs' -> do
        ss' <- unifyingSubstitutions t t'
        solve (ss' `compose` ss) (apply ss' cs')

compose :: Refinable t t => Substitutions t -> Substitutions t -> Substitutions t
(Substitutions ss') `compose` (Substitutions ss) = Substitutions $ Map.map (apply (Substitutions ss)) ss' `Map.union` ss

ensure :: Monad m => Constraint t -> InferT m t ()
ensure c = tell [c]

unify :: Monad m => t -> t -> InferT m t ()
unify t1 t2 = ensure $ t1 :~ t2

unifyMany :: (Unifiable t, Refinable t t, Show t) => [t] -> [t] -> Solve (Substitutions t)
unifyMany [] [] = return $ Substitutions Map.empty
unifyMany (t : ts) (t' : ts') =
  do
    ss <- unifyingSubstitutions t t'
    ss' <- unifyMany (apply ss ts) (apply ss ts')
    return (ss' `compose` ss)
unifyMany t1 t2 = throwError $ pack $ "unification failed: " ++ show (t1, t2)

bind :: (Eq t, Unifiable t, Show t, Template t) => Name -> t -> Solve (Substitutions t)
bind v t
  | isVar v t = return $ Substitutions Map.empty
  | v `Set.member` freeTypeVars t = throwError $ pack $ "binding failed: " ++ show (v, t)
  | otherwise = return (Substitutions $ Map.singleton v t)

lookup ::
  (Show t, Refinable t t, Unifiable t, Template t, MonadState [Span -> t] m) =>
  Name ->
  InferT m t t
lookup v =
  asks (Map.lookup v . locals) >>= \case
    Nothing -> throwError . pack $ show v ++ " is undefined"
    Just s -> instantiate s

with :: Monad m => [(Name, t)] -> InferT m t a -> InferT m t a
with vs = local (\ctx -> ctx {locals = foldr extendContext (locals ctx) vs})
  where
    extendContext (v, op) = Map.insert v op . Map.delete v

fresh :: (MonadState (FreshTypeVarStream t) m) => Span -> m t
fresh s = do
  stream <- get
  put $ tail stream
  return $ head stream s

instance (Functor f, Refinable t t) => Refinable [f t] t where
  apply ss = fmap (apply ss)

instance (Functor f, Refinable t t) => Refinable (f t) t where
  apply ss = fmap (apply ss)

instance (Foldable f, Template t) => Template (f t) where
  freeTypeVars = foldr (Set.union . freeTypeVars) Set.empty
  instantiate = error "Not implemented"
