{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

module Generate (buildModule) where

import Control.Monad.Reader (MonadReader (ask, local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Char
import Data.Function
import Data.List (elemIndex)
import qualified Data.Map as Map
import Data.String
import Data.Text hiding (filter, foldr, head, length, tail, unlines, zip)
import Data.Text.Lazy (toStrict)
import qualified IR as Rush
import LLVM.AST hiding (Add, alignment, callingConvention, function, functionAttributes, metadata, returnAttributes, type')
import LLVM.AST.AddrSpace
import LLVM.AST.CallingConvention
import LLVM.AST.Constant (Constant (Add, type'))
import LLVM.AST.Constant hiding (Add, ICmp, type')
import LLVM.AST.Global (Global (Function, GlobalVariable, addrSpace, alignment, basicBlocks, callingConvention, comdat, dllStorageClass, functionAttributes, garbageCollectorName, initializer, isConstant, linkage, metadata, name, parameters, personalityFunction, prefix, returnAttributes, section, threadLocalMode, type', unnamedAddr, visibility))
import LLVM.AST.IntegerPredicate
import LLVM.AST.Linkage
import LLVM.AST.Type
import LLVM.AST.Typed (Typed (typeOf))
import LLVM.AST.Visibility
import LLVM.IRBuilder hiding (buildModule, fresh)
import LLVM.Prelude hiding (EQ, lookup)
import Pattern
import Test.Hspec
import Prelude hiding (EQ, lookup)

data BuildState = BuildState
  { globals :: Map.Map Text Operand,
    names :: [Text]
  }

freshNames :: [Text]
freshNames = pack . ("__" ++) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

fresh :: (MonadState BuildState m) => m Text
fresh = do
  state <- get
  put $ state {names = tail $ names state}
  return $ head $ names state

data Locals = Locals {locals :: Map.Map Text Operand, closure :: Maybe Operand, captures :: [Text]}

type Build = ModuleBuilderT (ReaderT Locals (State BuildState))

buildModule :: String -> [Rush.Named Rush.Type] -> Module
buildModule name =
  flip evalState (BuildState Map.empty freshNames)
    . flip runReaderT (Locals Map.empty Nothing [])
    . buildModuleT (fromString name)
    . withPanic
    . mapM_ buildItem

withPanic :: (MonadModuleBuilder m, MonadReader Locals m) => m b -> m b
withPanic build = do
  panic <- extern (fromString "panic") [] VoidType
  with [("panic", panic)] build

panic :: (Monad m, MonadIRBuilder m, MonadReader Locals m, MonadState BuildState m, MonadModuleBuilder m) => m ()
panic = const unreachable =<< flip call [] =<< lookup "panic"

buildItem :: Rush.Named Rush.Type -> Build Operand
buildItem item@(Rush.Named name constant) = case constant of
  Rush.CNum n ty ->
    define name
      <$> global (fromText name) (asValue ty)
      $ parseIntConst n
  Rush.CFn tc@(Rush.TStruct caps) (x, tx) b -> do
    define name $
      function
        (fromText name)
        [(asArg tc, fromText "closure"), (asArg tx, fromText x)]
        (asValue $ Rush.typeOf b)
        (\[c', x'] -> bind caps c' $ with [(x, x')] (ret =<< mkVal =<< buildExpr b))
  Rush.CFn Rush.TUnit (x, tx) b -> do
    define name $
      function
        (fromText name)
        [(asArg tx, fromText x)]
        (asValue $ Rush.typeOf b)
        (\[x'] -> with [(x, x')] $ ret =<< mkVal =<< buildExpr b)
  e -> error $ "unreachable Item: " ++ unpack name ++ ": " ++ show e

closureFields :: (Monad m, MonadIRBuilder m, MonadModuleBuilder m) => Operand -> Map.Map Text Rush.Type -> m [(Text, Operand)]
closureFields closureOp fields = mapM get (zip [0 ..] $ Map.toAscList fields)
  where
    get (i, (x, tx)) = (x,) <$> (flip load 0 =<< gep closureOp [int32 0, int32 i])

buildExpr ::
  ( MonadReader Locals m,
    MonadState BuildState m,
    MonadIRBuilder m,
    MonadFix m,
    MonadModuleBuilder m
  ) =>
  Rush.Expr Rush.Type ->
  m Operand
buildExpr e =
  case e of
    Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
    Rush.Tup xs -> do
      t <- alloca (asValue $ Rush.typeOf e) Nothing 0
      xs' <- mapM buildExpr xs
      forM_
        (zip [0 ..] xs')
        (\(i, x) -> join $ store <$> gep t [int32 0, int32 i] <*> pure 0 <*> pure x)
      pure t
    Rush.Var v _ -> lookup v
    Rush.Add a b -> join $ add <$> (mkVal =<< buildExpr a) <*> (mkVal =<< buildExpr b)
    Rush.Match xs arms -> mdo
      let xs' = (\(Rush.Var x _) -> x) <$> xs
      matchBlock <- block
      tried <- buildMatchArms returnBlock matchBlock xs' [] arms
      returnBlock <- block `named` "return"
      phi tried
    Rush.App ty f x -> do
      f' <- buildExpr f
      x' <- mkArg (Rush.typeOf x) =<< buildExpr x
      case Rush.typeOf f of
        tc@(Rush.TClosure f' _ _) -> do
          c' <- mkArg tc =<< buildExpr f
          flip call [(c', []), (x', [])] =<< lookup f'
        Rush.TFn tc tx tb -> flip call [(x', [])] =<< buildExpr f
        _ -> error "unreachable"
    c@(Rush.Closure name caps _) -> do
      closureStorage <- do
        let tc' = asValue $ Rush.typeOf c
        alloca tc' Nothing 0
      forM_
        (zip [0 ..] (Map.keys caps))
        ( \(i, fieldName) -> do
            fieldVal <- lookup fieldName
            fieldPtr <- gep closureStorage [int32 0, int32 i]
            store fieldPtr 0 fieldVal
        )
      pure closureStorage
    e -> error $ "TODO: " ++ show e

deref :: MonadIRBuilder m => Operand -> m Operand
deref op = case op of
  LocalReference PointerType {} _ -> load op 0
  _ -> return op

buildMatchArms ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  Name ->
  [Text] ->
  [(Operand, Name)] ->
  [([Pattern.Pattern Rush.Type], Rush.Expr Rush.Type)] ->
  m [(Operand, Name)]
buildMatchArms _ thisBlock _ tried [] = do
  panic
  return tried
buildMatchArms returnBlock thisBlock xs tried ((ps, b) : arms) = mdo
  thisBranch <- buildMatchArm returnBlock thisBlock nextBlock xs ps b
  nextBlock <- block
  buildMatchArms returnBlock nextBlock xs (thisBranch : tried) arms

buildMatchArm ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  Name ->
  Name ->
  [Text] ->
  [Pattern.Pattern Rush.Type] ->
  Rush.Expr Rush.Type ->
  m (Operand, Name)
buildMatchArm returnBlock thisBlock _ [] [] e = do
  result <- buildExpr e
  br returnBlock
  return (result, thisBlock)
buildMatchArm returnBlock thisBlock nextBlock (x : xs) (p : ps) e = case p of
  Binding x' _ -> do
    x'' <- lookup x
    with [(x', x'')] $ buildMatchArm returnBlock thisBlock nextBlock xs ps e
  Num n _ -> mdo
    let n' = parseInt n
    x' <- lookup x
    matches <- icmp EQ x' n'
    condBr matches continueBlock nextBlock
    continueBlock <- block
    buildMatchArm returnBlock continueBlock nextBlock xs ps e
  Tup ps' -> case ps' of
    [] -> buildMatchArm returnBlock thisBlock nextBlock xs ps e
    ps' -> do
      x' <- lookup x
      xs' <- mapM (const fresh) ps'
      xs'' <- mapM (\(i, p') -> gep x' [int32 0, int32 i]) (zip [0 ..] ps')
      with (zip xs' xs'') $ buildMatchArm returnBlock thisBlock nextBlock (xs' ++ xs) (ps' ++ ps) e
buildMatchArm _ _ _ x p e = error $ "unreachable: buildMatchArm .. " ++ show (x, p, e)

asValue :: Rush.Type -> Type
asValue = \case
  Rush.TInt _ -> i64
  Rush.TTup tys -> (StructureType False $ asValue <$> tys)
  Rush.TVar _ _ -> error "unreachable: asValue TVar"
  Rush.TStruct fields -> (StructureType False $ asValue <$> Map.elems fields)
  Rush.TClosure _ caps _ -> (StructureType False $ asValue <$> Map.elems caps)
  Rush.TFn c@Rush.TClosure {} a b -> PointerType (FunctionType (asValue b) [asArg c, asArg a] False) (AddrSpace 0)
  Rush.TFn Rush.TUnit a b -> PointerType (FunctionType (asValue b) [asArg a] False) (AddrSpace 0)
  _ -> error "unreachable"

asArg :: Rush.Type -> Type
asArg ty
  | passedByValue ty = asValue ty
  | otherwise = PointerType (asValue ty) (AddrSpace 0)

mkArg :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkArg ty
  | passedByValue ty = mkVal
  | otherwise = mkRef

mkVal :: MonadIRBuilder m => Operand -> m Operand
mkVal op = case typeOf op of
  PointerType {} -> deref op
  _ -> pure op

mkRef :: (MonadIRBuilder m) => Operand -> m Operand
mkRef op = case typeOf op of
  PointerType {} -> pure op
  _ -> do
    ref <- alloca (typeOf op) Nothing 0
    store ref 0 op
    pure ref

passedByValue :: Rush.Type -> Bool
passedByValue = \case
  Rush.TTup {} -> False
  Rush.TStruct {} -> False
  Rush.TClosure {} -> False
  _ -> True

parseInt :: Text -> Operand
parseInt = ConstantOperand . parseIntConst

parseIntConst :: Text -> Constant
parseIntConst = Int 64 . read . unpack

fromText :: (IsString a) => Text -> a
fromText = fromString . unpack

with :: (MonadReader Locals m) => [(Text, Operand)] -> m a -> m a
with vs = local (\ctx -> ctx {locals = foldr extendContext (locals ctx) vs})
  where
    extendContext (v, op) = Map.insert v op . Map.delete v

bind :: (MonadReader Locals m) => Map.Map Text Rush.Type -> Operand -> m a -> m a
bind caps op = local (\ctx -> ctx {closure = Just op, captures = fst <$> Map.toAscList caps})

lookup :: (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadModuleBuilder m) => Text -> m Operand
lookup name =
  do
    globals' <- gets globals
    locals' <- asks locals
    closure' <- asks closure
    captures' <- asks captures
    let global = Map.lookup name globals'
    let local = Map.lookup name locals'
    let captureIndex = toEnum <$> elemIndex name captures'
    capture <- mapM (\(c, i) -> flip load 0 =<< gep c [int32 0, int32 i]) $ (,) <$> closure' <*> captureIndex
    let err =
          unpack name ++ " not found in\n"
            ++ "globals:\n"
            ++ unlines (show <$> Map.toAscList globals')
            ++ "\nlocals:\n"
            ++ unlines (show <$> Map.toAscList locals')
    return $ fromMaybe (error err) (local <|> capture <|> global)

define :: (MonadState BuildState m) => Text -> m Operand -> m Operand
define name op = do
  op <- op
  state <- get
  put (state {globals = Map.insert name op (globals state)})
  pure op
