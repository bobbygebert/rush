{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}

module Generate (buildModule) where

import qualified Constant
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Char
import Data.Function
import qualified Data.Map as Map
import Data.String
import Data.Text hiding (foldr, head, length, tail, zip)
import Data.Text.Lazy (toStrict)
import qualified Expression as Rush
import LLVM.AST hiding (Add, alignment, callingConvention, function, functionAttributes, metadata, returnAttributes, type')
import LLVM.AST.AddrSpace
import LLVM.AST.CallingConvention
import LLVM.AST.Constant (Constant (Add))
import LLVM.AST.Constant hiding (Add, ICmp, type')
import LLVM.AST.Global (Global (Function, GlobalVariable, addrSpace, alignment, basicBlocks, callingConvention, comdat, dllStorageClass, functionAttributes, garbageCollectorName, initializer, isConstant, linkage, metadata, name, parameters, personalityFunction, prefix, returnAttributes, returnType, section, threadLocalMode, type', unnamedAddr, visibility))
import LLVM.AST.IntegerPredicate
import LLVM.AST.Linkage
import LLVM.AST.Type
import LLVM.AST.Typed (typeOf)
import LLVM.AST.Visibility
import LLVM.IRBuilder hiding (buildModule, fresh)
import LLVM.Prelude hiding (EQ, lookup)
import Pattern
import Test.Hspec
import qualified Type as Rush
import Prelude hiding (EQ, lookup)

data BuilderState = BuilderState
  { globals :: Vars,
    names :: [Text]
  }

freshNames :: [Text]
freshNames = pack . ("__" ++) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

fresh :: (MonadState BuilderState m) => m Text
fresh = do
  state <- get
  put $ state {names = tail $ names state}
  return $ head $ names state

type Vars = Map.Map Text Operand

type Builder = ModuleBuilderT (ReaderT Vars (State BuilderState))

buildModule :: String -> [Constant.Named] -> Module
buildModule name =
  flip evalState (BuilderState Map.empty freshNames)
    . flip runReaderT Map.empty
    . buildModuleT (fromString name)
    . withPanic
    . mapM_ buildItem

withPanic :: (MonadModuleBuilder m, MonadReader Vars m) => m b -> m b
withPanic build = do
  panic <- extern (fromString "panic") [] VoidType
  with [("panic", panic)] build

panic :: (Monad m, MonadIRBuilder m, MonadReader Vars m, MonadState BuilderState m) => m ()
panic = const unreachable =<< flip call [] =<< lookup "panic"

buildItem :: Constant.Named -> Builder Operand
buildItem (Constant.Named name e) = case e of
  Constant.Num n _ ->
    define name
      <$> global (fromText name) i64
      $ parseIntConst n
  Constant.Lambda (x, tx) b -> do
    defineUncurried name (Rush.Lambda (x, tx) b)
    define name $
      function
        (fromText name)
        [(i64, fromText x)]
        i64
        (\[x'] -> with [(x, x')] $ ret =<< buildExpr b)

defineUncurried :: Text -> Rush.Expr Rush.Type -> ModuleBuilderT (ReaderT Vars (State BuilderState)) Operand
defineUncurried name e =
  function
    (fromText mangledName)
    argDecls
    i64
    (\args' -> with (zip argNames args') $ ret =<< buildExpr b)
  where
    mangledName = pack $ "__" ++ unpack name
    argNames = fst <$> xs
    argDecls = (i64,) . fromText <$> argNames
    xs = flattenArgs e
    b = getBody e
    flattenArgs = \case
      Rush.Lambda (x, tx) b -> (x, tx) : flattenArgs b
      _ -> []
    getBody = \case
      Rush.Lambda _ b -> getBody b
      b -> b

buildExpr ::
  ( MonadReader Vars m,
    MonadState BuilderState m,
    MonadIRBuilder m,
    MonadFix m
  ) =>
  Rush.Expr c ->
  m Operand
buildExpr = \case
  Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
  Rush.Var v _ -> lookup v
  Rush.Add a b -> join $ add <$> buildExpr a <*> buildExpr b
  Rush.Match xs [ps] e -> mdo
    result <- buildMatchArm returnB panicB ((\(Rush.Var x _) -> x) <$> xs) ps e
    panicB <- block `named` "panic"
    panic
    returnB <- block `named` "return"
    return result
  Rush.Match (_ : _) (_ : _ : _) _ -> error "Match trees are not implemented."
  Rush.Match (_ : _ : _) _ _ -> error "Match on multiple paramters not implemented."
  Rush.Match {} -> error "Match on expressions not implemented."
  -- TODO: move error to panic message.
  Rush.Lambda (x, _) b -> return $ parseInt "0" -- error "Lambda expressions not implemented."
  Rush.App _ f x -> do
    f' <- buildExpr f
    x <- buildExpr x
    call f' [(x, [])]

buildMatchArm ::
  (MonadReader Vars m, MonadState BuilderState m, MonadIRBuilder m, MonadFix m) =>
  Name ->
  Name ->
  [Text] ->
  [Pattern.Pattern c] ->
  Rush.Expr c ->
  m Operand
buildMatchArm returnB _ [] [] e = do
  result <- buildExpr e
  br returnB
  return result
buildMatchArm returnB panicB (x : xs) (p : ps) e = case p of
  Binding x' _ -> do
    x'' <- lookup x
    with [(x', x'')] $ buildMatchArm returnB panicB xs ps e
  Num n _ -> mdo
    let n' = parseInt n
    x' <- lookup x
    matches <- icmp EQ x' n'
    condBr matches continueB panicB
    continueB <- block
    buildMatchArm returnB panicB xs ps e
buildMatchArm _ _ _ _ _ = error "unreachable"

parseInt :: Text -> Operand
parseInt = ConstantOperand . parseIntConst

parseIntConst :: Text -> Constant
parseIntConst = Int 64 . read . unpack

fromText :: (IsString a) => Text -> a
fromText = fromString . unpack

with :: (MonadReader Vars m) => [(Text, Operand)] -> m a -> m a
with vs = local (\env -> foldr (\(v, op) -> Map.insert v op . Map.delete v) env vs)

lookup :: (MonadReader Vars m, MonadState BuilderState m) => Text -> m Operand
lookup name =
  fromMaybe <$> (fromMaybe (error err) <$> global) <*> local
  where
    err = unpack name ++ " not found"
    global = gets $ Map.lookup name . globals
    local = asks $ Map.lookup name

define :: (MonadState BuilderState m) => Text -> m Operand -> m Operand
define name op = do
  op <- op
  state <- get
  put (state {globals = Map.insert name op (globals state)})
  pure op
