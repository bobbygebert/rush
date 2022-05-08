{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Generate (buildModule) where

import Control.Monad.Reader (MonadReader (ask, local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Char
import Data.Function
import Data.List (elemIndex)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.String
import Data.Text hiding (filter, foldr, head, length, null, tail, unlines, zip)
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
import LLVM.Prelude hiding (EQ, lookup, null)
import LLVM.Pretty (ppll)
import Parser (emptySpan)
import Pattern
import Test.Hspec
import Prelude hiding (EQ, lookup, null)

data BuildState = BuildState
  { globals :: Map.Map Text Operand,
    types :: Set.Set Name,
    names :: [Text]
  }

data Locals = Locals {locals :: Map.Map Text Operand, closure :: Maybe Operand, captures :: [Text]}
  deriving (Show)

type Build = ModuleBuilderT (ReaderT Locals (State BuildState))

buildModule :: String -> [Rush.Named Rush.Type] -> Module
buildModule name =
  flip evalState (BuildState Map.empty Set.empty freshNames)
    . flip runReaderT (Locals Map.empty Nothing [])
    . buildModuleT (fromString name)
    . withPanic
    . withMalloc
    . (mapM_ buildItem <=< mapM declareItem)

declareItem :: Rush.Named Rush.Type -> Build (Rush.Named Rush.Type)
declareItem item@(Rush.Named name constant) =
  item <$ declare name (Rush.typeOf (Rush.unConst constant))

buildItem :: Rush.Named Rush.Type -> Build Operand
buildItem item@(Rush.Named name constant) =
  case constant of
    Rush.CNum n ty -> do
      define name
        =<< global (fromText name)
        <$> asValue ty
        <*> pure (parseIntConst n)
    Rush.CFn tc@(Rush.TStruct caps) (x, tx) b -> do
      define name
        =<< function (fromText name)
        <$> (zip <$> mapM asArg [tc, tx] <*> pure (fromText <$> ["closure", x]))
        <*> asValue (Rush.typeOf b)
        <*> pure (\[c', x'] -> bind caps c' $ with [(x, x')] (ret =<< mkRet (Rush.typeOf b) =<< buildExpr b))
    Rush.CFn Rush.TUnit (x, tx) b -> do
      define name
        =<< function (fromText name)
        <$> (asArg tx <&> (: []) . (,fromText x))
        <*> asValue (Rush.typeOf b)
        <*> pure (\[x'] -> with [(x, x')] $ ret =<< mkRet (Rush.typeOf b) =<< buildExpr b)
    e -> error $ "unreachable Item: " ++ unpack name ++ ": " ++ show e

buildExpr ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Rush.Expr Rush.Type ->
  m Operand
buildExpr e =
  case e of
    Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
    Rush.Var v _ -> lookup v
    Rush.Add a b ->
      join $
        add
          <$> (mkVal (Rush.typeOf a) =<< buildExpr a)
          <*> (mkVal (Rush.typeOf b) =<< buildExpr b)
    Rush.Tup xs -> do
      t <- (\ty -> alloca ty Nothing 0) =<< asValue (Rush.typeOf e)
      xs' <- mapM buildExpr xs
      forM_
        (zip3 [0 ..] xs' (Rush.typeOf <$> xs))
        (\(i, x, tx) -> join $ store <$> gep t [int32 0, int32 i] <*> pure 0 <*> mkVal tx x)
      pure t
    Rush.List tx xs -> case xs of
      [] -> inttoptr (int64 0) . asPtr =<< listType tx
      x : xs -> do
        list <- malloc (Rush.typeOf e)
        head <- gep list [int32 0, int32 0]
        tail <- gep list [int32 0, int32 1]
        store head 0 =<< mkVal tx =<< buildExpr x
        store tail 0 =<< mkRef =<< buildExpr (Rush.List tx xs)
        pure list
    Rush.Cons h t -> do
      list <- malloc (Rush.typeOf e)
      head <- gep list [int32 0, int32 0]
      tail <- gep list [int32 0, int32 1]
      store head 0 =<< mkVal (Rush.typeOf h) =<< buildExpr h
      store tail 0 =<< mkRef =<< buildExpr t
      pure list
    Rush.Match xs arms -> mdo
      let xs' = (\(Rush.Var x _) -> x) <$> xs
      block
      tried <- buildMatchArms returnBlock xs' [] arms
      returnBlock <- block `named` "return"
      phi tried
    Rush.App ty f x -> do
      f' <- buildExpr f
      x' <- mkArg (Rush.typeOf x) =<< buildExpr x
      case Rush.typeOf f of
        Rush.TFn tu@(Rush.TUnion tcs) _ _ -> mdo
          union <- buildExpr f
          disc' <- deref =<< gep union [int32 0, int32 0]
          closureStorage <- gep union [int32 0, int32 1]
          arg <- mkArg (Rush.typeOf x) =<< buildExpr x
          br matchBlock
          let arms = zip (int64 <$> [0 ..]) (Map.toList tcs)
          matchBlock <- block
          tried <- callUnionClosure returnBlock closureStorage disc' arg [] arms
          returnBlock <- block `named` "return"
          phi tried
        tc@(Rush.TClosure f' _ _) -> do
          c' <- mkArg tc =<< buildExpr f
          flip call [(c', []), (x', [])] =<< mkRef =<< lookup f'
        Rush.TFn Rush.TUnit tx tb -> flip call [(x', [])] =<< mkRef =<< buildExpr f
        ty -> error $ "unreachable: " ++ show ty
    c@(Rush.Closure name caps _) -> do
      closureStorage <- do
        tc' <- asValue (Rush.typeOf c)
        alloca tc' Nothing 0
      forM_ (zip3 [0 ..] (Map.keys caps) (Rush.typeOf <$> Map.elems caps)) $ \(i, fieldName, ty) -> do
        fieldVal <- mkVal ty =<< lookup fieldName
        fieldPtr <- gep closureStorage [int32 0, int32 i]
        store fieldPtr 0 fieldVal
      pure closureStorage
    u@(Rush.Union tcs disc val) -> do
      unionStorage <- do
        tc' <- asValue (Rush.typeOf u)
        alloca tc' Nothing 0
      disc' <- gep unionStorage [int32 0, int32 0]
      closure <-
        join
          ( bitcast
              <$> gep unionStorage [int32 0, int32 1]
              <*> (asPtr <$> asField (Rush.typeOf val))
          )
      store disc' 0 $ fromJust $ Map.lookup disc (Map.fromList (zip (Map.keys tcs) (int32 <$> [0 ..])))
      store closure 0 =<< mkVal (Rush.typeOf val) =<< buildExpr val
      pure unionStorage
    e -> error $ "unreachable: " ++ show e

buildMatchArms ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  [Text] ->
  [(Operand, Name)] ->
  [([Pattern.Pattern Rush.Type], Rush.Expr Rush.Type)] ->
  m [(Operand, Name)]
buildMatchArms _ _ tried [] = do
  panic
  return tried
buildMatchArms returnBlock xs tried ((ps, b) : arms) = mdo
  thisBranch <- buildMatchArm returnBlock nextBlock xs ps b
  nextBlock <- block
  buildMatchArms returnBlock xs (thisBranch : tried) arms
  where
    buildMatchArm returnBlock _ [] [] e = do
      result <- buildExpr e
      br returnBlock
      (result,) <$> currentBlock
    buildMatchArm returnBlock nextBlock (x : xs) (p : ps) e = case p of
      Binding x' _ -> do
        x'' <- lookup x
        with [(x', x'')] $ buildMatchArm returnBlock nextBlock xs ps e
      Num n _ -> mdo
        let n' = parseInt n
        x' <- lookup x
        matches <- icmp EQ x' n'
        condBr matches continueBlock nextBlock
        continueBlock <- block
        buildMatchArm returnBlock nextBlock xs ps e
      Tup ps' -> case ps' of
        [] -> buildMatchArm returnBlock nextBlock xs ps e
        ps' -> do
          x' <- mkRef =<< lookup x
          xs' <- mapM (const fresh) ps'
          xs'' <- mapM (\(i, p') -> gep x' [int32 0, int32 i]) (zip [0 ..] ps')
          with (zip xs' xs'') $ buildMatchArm returnBlock nextBlock (xs' ++ xs) (ps' ++ ps) e
      List tx ps' -> case ps' of
        [] -> mdo
          node <- flip ptrtoint i64 =<< mkRef =<< lookup x
          matches <- icmp EQ node (int64 0)
          condBr matches continueBlock nextBlock
          continueBlock <- block
          buildMatchArm returnBlock nextBlock xs ps e
        hp : tps -> do
          node <- mkRef =<< lookup x
          h <- fresh
          h' <- gep node [int32 0, int32 0]
          t <- fresh
          t' <- gep node [int32 0, int32 1]
          let tps' = List tx tps
          with [(h, h'), (t, t')] $
            buildMatchArm returnBlock nextBlock (h : t : xs) (hp : tps' : ps) e
      Cons hp tp -> do
        node <- mkRef =<< lookup x
        h <- fresh
        h' <- gep node [int32 0, int32 0]
        t <- fresh
        t' <- gep node [int32 0, int32 1]
        with [(h, h'), (t, t')] $
          buildMatchArm returnBlock nextBlock (h : t : xs) (hp : tp : ps) e
    buildMatchArm _ _ x p e = error $ "unreachable: buildMatchArm .. " ++ show (x, p, e)

callUnionClosure ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  Operand ->
  Operand ->
  Operand ->
  [(Operand, Name)] ->
  [(Operand, (Text, Rush.Type))] ->
  m [(Operand, Name)]
callUnionClosure returnBlock storage disc arg tried (arm : arms) = mdo
  thisBranch <- buildMatchArm returnBlock nextBlock storage disc arg arm
  nextBlock <- block
  callUnionClosure returnBlock storage disc arg (thisBranch : tried) arms
  where
    buildMatchArm returnBlock nextBlock storage disc arg (i, (f, ty)) = mdo
      matches <- icmp EQ disc i
      condBr matches callBlock nextBlock
      callBlock <- block
      closure <- join (bitcast <$> gep storage [int32 0, int32 0] <*> (asPtr <$> asField ty))
      result <- flip call [(closure, []), (arg, [])] =<< mkRef =<< lookup f
      br returnBlock
      return (result, callBlock)
callUnionClosure _ _ _ _ tried [] = do
  panic
  return tried

listType :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
listType tx = do
  state <- get
  name <- fromText . ("List " <>) . toStrict . ppll <$> asValue ty
  tx' <- asValue tx
  ty' <-
    if not $ name `Set.member` types state
      then typedef name $ Just $ StructureType False [tx', asPtr (NamedTypeReference name)]
      else pure $ NamedTypeReference name
  put state {types = Set.insert name (types state)}
  pure ty'
  where
    ty = Rush.withSpan emptySpan $ case tx of
      Rush.TFn tc _ _ -> tc
      _ -> tx

asValue :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asValue ty@Rush.TList {} = asPtr <$> asStorage ty
asValue ty = asStorage ty

asStorage :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asStorage = \case
  Rush.TInt _ -> pure i64
  Rush.TTup tys -> StructureType False <$> mapM asValue tys
  Rush.TList tx -> listType tx
  Rush.TVar {} -> error "unreachable: asValue TVar"
  Rush.TStruct fields -> StructureType False <$> mapM asField (Map.elems fields)
  Rush.TClosure _ caps _ -> StructureType False <$> mapM asField (Map.elems caps)
  Rush.TUnion tys -> pure $ StructureType False [i32, ArrayType 8 i64]
  Rush.TFn c@Rush.TUnion {} a b -> asValue c
  Rush.TFn c@Rush.TStruct {} a b -> asValue c
  ty -> error $ "unreachable: " ++ show ty

asField :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asField = \case
  Rush.TList tx -> asPtr <$> listType tx
  ty -> asValue ty

asArg :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asArg ty
  | passedByValue ty = asValue ty
  | otherwise = flip PointerType (AddrSpace 0) <$> asValue ty

asPtr :: Type -> Type
asPtr ty = PointerType ty (AddrSpace 0)

mkArg :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkArg ty
  | passedByValue ty = mkVal ty
  | otherwise = mkRef

mkVal :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkVal Rush.TList {} op = mkRef op
mkVal ty op = case typeOf op of
  PointerType {} -> deref op
  _ -> pure op

mkRet :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkRet = mkVal

mkRef :: (MonadIRBuilder m) => Operand -> m Operand
mkRef op = case typeOf op of
  PointerType PointerType {} _ -> mkRef =<< deref op
  PointerType {} -> pure op
  _ -> do
    -- XXX
    ref <- alloca (typeOf op) Nothing 0
    store ref 0 op
    pure ref

deref :: MonadIRBuilder m => Operand -> m Operand
deref op = case op of
  LocalReference PointerType {} _ -> load op 0
  _ -> return op

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
    global <- gets $ Map.lookup name . globals
    local <- asks $ Map.lookup name . locals
    closure <- asks closure
    captureIndex <- asks ((fmap toEnum . elemIndex name) . captures)
    capture <- mapM (\(c, i) -> flip load 0 =<< gep c [int32 0, int32 i]) $ (,) <$> closure <*> captureIndex
    return $ (local <|> capture <|> global) & fromMaybe (error $ "undefined: " <> unpack name)

declare :: (MonadState BuildState m, MonadModuleBuilder m) => Text -> Rush.Type -> m ()
declare name (Rush.TFn tc tx tb) = do
  ty <- asPtr <$> (FunctionType <$> asValue tb <*> txs <*> pure False)
  let decl = ConstantOperand (GlobalReference ty (fromText name))
  state <- get
  put (state {globals = Map.insert name decl (globals state)})
  where
    txs = mapM asArg $ case tc of
      c@Rush.TUnion {} -> [tc, tx]
      c@Rush.TStruct {} -> [tc, tx]
      Rush.TUnit -> [tx]
      _ -> error "unreachable"
declare _ _ = pure ()

define :: (MonadState BuildState m) => Text -> m Operand -> m Operand
define name op = do
  op <- op
  state <- get
  put (state {globals = Map.insert name op (globals state)})
  pure op

freshNames :: [Text]
freshNames = pack . ("__" ++) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

fresh :: (MonadState BuildState m) => m Text
fresh = do
  state <- get
  put $ state {names = tail $ names state}
  return $ head $ names state

withPanic :: (MonadModuleBuilder m, MonadReader Locals m) => m b -> m b
withPanic build = do
  panic <- extern (fromString "panic") [] VoidType
  with [("panic", panic)] build

panic ::
  (MonadIRBuilder m, MonadReader Locals m, MonadState BuildState m, MonadModuleBuilder m) =>
  m ()
panic = const unreachable =<< flip call [] =<< lookup "panic"

withMalloc :: (MonadModuleBuilder m, MonadReader Locals m) => m b -> m b
withMalloc build = do
  panic <- extern (fromString "malloc") [i64] (asPtr i8)
  with [("malloc", panic)] build

malloc ::
  (MonadIRBuilder m, MonadReader Locals m, MonadState BuildState m, MonadModuleBuilder m) =>
  Rush.Type ->
  m Operand
malloc ty = do
  ty' <- asStorage ty
  ptr <-
    uncurry call
      =<< (,)
        <$> lookup "malloc"
        <*> ((: []) . (,[]) <$> sext (ConstantOperand (sizeof ty')) i64)
  bitcast ptr (asPtr ty')
