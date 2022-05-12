{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Generate (buildModule) where

import Control.Monad.Reader (MonadReader (ask, local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Bifunctor
import Data.Char
import Data.Function
import Data.List (elemIndex)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.String
import Data.Text hiding (filter, foldr, head, length, null, replicate, tail, take, unlines, zip)
import Data.Text.Lazy (toStrict)
import Debug.Trace
import GHC.Stack (HasCallStack, callStack, getCallStack)
import qualified IR as Rush
import LLVM.AST hiding (Add, alignment, callingConvention, function, functionAttributes, metadata, returnAttributes, type')
import LLVM.AST.AddrSpace
import LLVM.AST.CallingConvention
import LLVM.AST.Constant (Constant (Add, type'))
import LLVM.AST.Constant hiding (Add, ICmp, type')
import LLVM.AST.Global (Global (Function, GlobalVariable, addrSpace, alignment, basicBlocks, callingConvention, comdat, dllStorageClass, functionAttributes, garbageCollectorName, initializer, isConstant, linkage, metadata, name, parameters, personalityFunction, prefix, returnAttributes, section, threadLocalMode, type', unnamedAddr, visibility))
import LLVM.AST.IntegerPredicate
import LLVM.AST.Linkage
import LLVM.AST.Type hiding (void)
import LLVM.AST.Typed (Typed (typeOf))
import LLVM.AST.Visibility
import LLVM.IRBuilder hiding (buildModule, fresh)
import LLVM.Prelude hiding (EQ, lookup, null)
import LLVM.Pretty (ppll)
import Span
import qualified Span as Rush
import Test.Hspec
import Prelude hiding (EQ, lookup, null)

data BuildState = BuildState
  { globals :: Map.Map Text Operand,
    types :: Set.Set Name,
    names :: [Text]
  }
  deriving (Show, Eq)

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

buildItem :: Rush.Named Rush.Type -> Build ()
buildItem item@(Rush.Named name constant) =
  trace ("building: " ++ show item) $
    case constant of
      Rush.CNum n ty ->
        define name
          =<< global (fromText name)
          <$> asValue ty
          <*> pure (parseIntConst n)
      Rush.CFn tc@(Rush.TData _ [(_, caps)]) (x, tx) b ->
        define name
          =<< function (fromText name)
          <$> (zip <$> mapM asArg [tc, tx] <*> pure (fromText <$> ["closure", x]))
          <*> asValue (Rush.typeOf b)
          <*> pure (\[c', x'] -> bind caps c' $ with [(x, x')] (ret =<< mkRet (Rush.typeOf b) =<< buildExpr b))
      Rush.CFn Rush.TUnit (x, tx) b ->
        define name
          =<< function (fromText name)
          <$> (asArg tx <&> (: []) . (,fromText x))
          <*> asValue (Rush.typeOf b)
          <*> pure (\[x'] -> with [(x, x')] $ ret =<< mkRet (Rush.typeOf b) =<< buildExpr b)
      Rush.CData _ ty@(Rush.TData n cs) [] -> do
        let disc = fromJust . Map.lookup name $ Map.fromList (zip (fst <$> cs) [0 ..])
        let storageSize = sizeInWords ty - 1
        let storage = case cs of
              [_] -> Struct Nothing False []
              _ ->
                Struct
                  Nothing
                  False
                  [Int 32 disc, Array i64 $ replicate storageSize (Int 64 0)]
        define name
          =<< global (fromText name)
          <$> asStorage ty
          <*> pure storage
      e -> error $ "unreachable Item: " ++ unpack name ++ ": " ++ show e

buildExpr ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Rush.Expr Rush.Type ->
  m Operand
buildExpr e = do
  let buildVal x = mkVal (Rush.typeOf x) =<< buildExpr x
  let buildBinOp op a b = join $ op <$> buildVal a <*> buildVal b
  case e of
    Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
    Rush.Var v _ -> lookup v
    Rush.Add a b -> buildBinOp add a b
    Rush.Sub a b -> buildBinOp sub a b
    Rush.Mul a b -> buildBinOp mul a b
    Rush.Div a b -> buildBinOp udiv a b
    Rush.Mod a b -> buildBinOp urem a b
    Rush.Tup xs -> do
      t <- (\ty -> alloca ty Nothing 0) =<< asStorage (Rush.typeOf e)
      xs' <- mapM buildExpr xs
      forM_
        (zip3 [0 ..] xs' (Rush.typeOf <$> xs))
        (\(i, x, tx) -> join $ store <$> gep t [int32 0, int32 i] <*> pure 0 <*> mkVal tx x)
      pure t
    Rush.Data c ty@(Rush.TData _ cs) xs -> do
      let disc = fromJust . Map.lookup c $ Map.fromList (zip (fst <$> cs) [0 ..])
      let storageSize = sizeInWords ty - 1
      struct <- malloc ty
      discStorage <- case cs of
        [_] -> pure struct
        _ -> gep struct [int32 0, int32 0]
      dataStorage <- case cs of
        [_] -> pure struct
        _ -> do
          store discStorage 0 (int32 disc)
          join $
            bitcast
              <$> gep struct [int32 0, int32 1]
              <*> (asPtr . StructureType False <$> mapM (asField . Rush.typeOf) xs)
      xs' <- mapM buildExpr xs
      forM_
        (zip3 [0 ..] xs' (Rush.typeOf <$> xs))
        ( \(i, x, tx) ->
            join $
              store
                <$> gep dataStorage [int32 0, int32 i] <*> pure 0 <*> pure x
        )
      pure struct
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
      x' <- mkArg (Rush.typeOf x) =<< buildExpr x
      case Rush.typeOf f of
        Rush.TFn Rush.TUnit tx tb -> flip call [(x', [])] =<< mkRef =<< buildExpr f
        tc@(Rush.TClosure f' _ _) -> do
          c' <- mkArg tc =<< buildExpr f
          flip call [(c', []), (x', [])] =<< mkRef =<< lookup f'
        Rush.TData _ tcs -> mdo
          closure <- mkRef =<< buildExpr f
          disc' <- deref =<< gep closure [int32 0, int32 0]
          closureStorage <- gep closure [int32 0, int32 1]
          arg <- mkArg (Rush.typeOf x) =<< buildExpr x
          br matchBlock
          let arms = zip (int64 <$> [0 ..]) (second (head . Map.elems) <$> tcs)
          matchBlock <- block
          tried <- callClosureSum returnBlock closureStorage disc' arg [] arms
          returnBlock <- block `named` "return"
          phi tried
        ty -> error $ "unreachable: " ++ show (f, ty)
    c@(Rush.Closure name caps _) -> do
      closureStorage <- do
        tc' <- asValue (Rush.typeOf c)
        alloca tc' Nothing 0
      forM_ (zip3 [0 ..] (Map.keys caps) (Rush.typeOf <$> Map.elems caps)) $ \(i, fieldName, ty) -> do
        fieldVal <- mkVal ty =<< lookup fieldName
        fieldPtr <- gep closureStorage [int32 0, int32 i]
        store fieldPtr 0 fieldVal
      pure closureStorage
    e -> error $ "unreachable: " ++ show e

buildMatchArms ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  [Text] ->
  [(Operand, Name)] ->
  [([Rush.Expr Rush.Type], Rush.Expr Rush.Type)] ->
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
      result <- mkArg (Rush.typeOf e) =<< buildExpr e
      br returnBlock
      (result,) <$> currentBlock
    buildMatchArm returnBlock nextBlock (x : xs) (p : ps) e = case p of
      Rush.Var x' _ -> do
        x'' <- lookup x
        with [(x', x'')] $ buildMatchArm returnBlock nextBlock xs ps e
      Rush.Num n _ -> mdo
        let n' = parseInt n
        x' <- lookup x
        matches <- icmp EQ x' n'
        condBr matches continueBlock nextBlock
        continueBlock <- block
        buildMatchArm returnBlock nextBlock xs ps e
      Rush.Tup ps' -> case ps' of
        [] -> buildMatchArm returnBlock nextBlock xs ps e
        ps' -> do
          x' <- mkRef =<< lookup x
          xs' <- mapM (const fresh) ps'
          xs'' <- mapM (\(i, p') -> gep x' [int32 0, int32 i]) (zip [0 ..] ps')
          with (zip xs' xs'') $ buildMatchArm returnBlock nextBlock (xs' ++ xs) (ps' ++ ps) e
      Rush.List tx ps' -> case ps' of
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
          let tps' = Rush.List tx tps
          with [(h, h'), (t, t')] $
            buildMatchArm returnBlock nextBlock (h : t : xs) (hp : tps' : ps) e
      Rush.Cons hp tp -> do
        node <- mkRef =<< lookup x
        h <- fresh
        h' <- gep node [int32 0, int32 0]
        t <- fresh
        t' <- gep node [int32 0, int32 1]
        with [(h, h'), (t, t')] $
          buildMatchArm returnBlock nextBlock (h : t : xs) (hp : tp : ps) e
      Rush.Data c ty@(Rush.TData _ cs) fs -> mdo
        let p' = Rush.Tup fs
        case cs of
          [_] -> do
            buildMatchArm returnBlock nextBlock (x : xs) (p' : ps) e
          _ -> mdo
            let disc =
                  int32 . fromJust . Map.lookup c $
                    Map.fromList (zip (fst <$> cs) [0 ..])
            struct <- mkRef =<< lookup x
            discMatches <- icmp EQ disc =<< deref =<< gep struct [int32 0, int32 0]
            condBr discMatches matchBlock nextBlock
            matchBlock <- block
            dataStorage <-
              join $
                bitcast
                  <$> gep struct [int32 0, int32 1]
                  <*> (asPtr <$> asField (Rush.typeOf $ Rush.Tup fs))
            x' <- fresh
            with [(x', dataStorage)] $
              buildMatchArm returnBlock nextBlock (x' : xs) (p' : ps) e
      ty -> error $ "unreachable: " ++ show ty
    buildMatchArm _ _ x p e = error $ "unreachable: buildMatchArm .. " ++ show (x, p, e)

callClosureSum ::
  (MonadReader Locals m, MonadState BuildState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
  Name ->
  Operand ->
  Operand ->
  Operand ->
  [(Operand, Name)] ->
  [(Operand, (Text, Rush.Type))] ->
  m [(Operand, Name)]
callClosureSum returnBlock storage disc arg tried (arm : arms) = mdo
  thisBranch <- buildMatchArm returnBlock nextBlock storage disc arg arm
  nextBlock <- block
  callClosureSum returnBlock storage disc arg (thisBranch : tried) arms
  where
    buildMatchArm returnBlock nextBlock storage disc arg (i, (f, ty)) = mdo
      matches <- icmp EQ disc i
      condBr matches callBlock nextBlock
      callBlock <- block
      closure <- (mkRef <=< join) $ bitcast storage <$> (asPtr <$> asStorage ty)
      result <- flip call [(closure, []), (arg, [])] =<< mkRef =<< lookup f
      br returnBlock
      return (result, callBlock)
callClosureSum _ _ _ _ tried [] = do
  panic
  return tried

listType :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
listType tx = do
  let ty = case tx of
        Rush.TFn tc _ _ -> tc
        _ -> tx
  name <- fromText . ("List " <>) . toStrict . ppll <$> asValue ty
  tx' <- asValue tx
  undefined <- state $ \state ->
    let state' = state {types = Set.insert name (types state)}
     in (types state /= types state', state')
  if undefined
    then typedef name $ Just $ StructureType False [tx', asPtr (NamedTypeReference name)]
    else pure $ NamedTypeReference name

dataType ::
  (MonadModuleBuilder m, MonadState BuildState m) =>
  Text ->
  [(Text, [Rush.Type])] ->
  m Type
dataType name cs = do
  let requiredSizeInWords =
        foldr max 0 (sum . ((sizeInWords <$>) . snd) <$> cs)
  ty <- case cs of
    [] -> error "unreachable"
    [(_, ts)] -> StructureType False <$> mapM asField ts
    cs -> pure $ StructureType False [i32, ArrayType (toEnum requiredSizeInWords) i64]
  let name' = fromText name
  undefined <- state $ \state ->
    let state' = state {types = Set.insert name' (types state)}
     in (types state /= types state', state')
  if undefined
    then typedef name' $ Just ty
    else pure $ NamedTypeReference name'

asValue :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asValue ty@Rush.TList {} = asPtr <$> asStorage ty
asValue ty@Rush.TData {} = asPtr <$> asStorage ty
asValue ty@Rush.TRef {} = asPtr <$> asStorage ty
asValue ty = asStorage ty

asStorage :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asStorage t = case t of
  Rush.TInt -> pure i64
  Rush.TTup tys -> StructureType False <$> mapM asValue tys
  Rush.TList tx -> listType tx
  Rush.TVar {} -> error "unreachable: asValue TVar"
  Rush.TClosure f cs _ -> dataType (fromText $ "_storage_" <> f) [("0", Map.elems cs)]
  Rush.TFn c@Rush.TData {} a b -> asValue c
  Rush.TData n cs -> dataType n (fmap (second $ fmap snd . Map.toAscList) cs)
  Rush.TRef n -> pure $ NamedTypeReference (fromText n)
  ty -> error $ "unreachable: " ++ show ty

sizeInWords :: Rush.Type -> Int
sizeInWords = \case
  Rush.TInt -> 1
  Rush.TTup tys -> sum $ sizeInWords <$> tys
  Rush.TList tx -> sizeInWords tx + 1
  Rush.TVar {} -> error "unreachable: asValue TVar"
  Rush.TClosure _ caps _ -> sum $ sizeInWords <$> Map.elems caps
  Rush.TData _ cs -> 1 + foldr max 0 (sum . (sizeInWords <$>) . snd <$> cs)
  Rush.TRef {} -> 1
  ty -> error $ "unreachable: " ++ show ty

asField :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asField = \case
  Rush.TList tx -> asPtr <$> listType tx
  Rush.TData name _ -> pure $ asPtr (NamedTypeReference (fromText name))
  Rush.TRef name -> pure $ asPtr (NamedTypeReference (fromText name))
  ty -> asValue ty

asArg :: (MonadModuleBuilder m, MonadState BuildState m) => Rush.Type -> m Type
asArg ty
  | passedByValue ty = asStorage ty
  | otherwise = flip PointerType (AddrSpace 0) <$> asStorage ty

asPtr :: Type -> Type
asPtr ty = PointerType ty (AddrSpace 0)

mkArg :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkArg ty
  | passedByValue ty = mkVal ty
  | otherwise = mkRef

mkVal :: MonadIRBuilder m => Rush.Type -> Operand -> m Operand
mkVal Rush.TList {} op = mkRef op
mkVal Rush.TData {} op = mkRef op
mkVal Rush.TRef {} op = mkRef op
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
  Rush.TList {} -> False
  Rush.TClosure {} -> False
  Rush.TData {} -> False
  Rush.TRef {} -> False
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
lookup name = do
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
  state $ \state -> ((), state {globals = Map.insert name decl (globals state)})
  where
    txs = mapM asArg $ case tc of
      c@Rush.TData {} -> [tc, tx]
      Rush.TUnit -> [tx]
      _ -> error "unreachable"
declare _ _ = pure ()

define :: (MonadState BuildState m) => Text -> m Operand -> m ()
define name op = do
  op <- op
  state $ \state -> ((), state {globals = Map.insert name op (globals state)})

freshNames :: [Text]
freshNames = pack . ("__" ++) <$> ([1 ..] >>= flip replicateM ['a' .. 'z'])

fresh :: (MonadState BuildState m) => m Text
fresh = state $ \state -> (head $ names state, state {names = tail $ names state})

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
