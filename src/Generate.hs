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
import Debug.Trace
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
import LLVM.AST.Typed (Typed (typeOf))
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

buildModule :: String -> [Constant.Named Rush.Type] -> Module
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

buildItem :: Constant.Named Rush.Type -> Builder Operand
buildItem (Constant.Named name ty e) = case e of
  Constant.Num n _ ->
    define name
      <$> global (fromText name) (asType ty)
      $ parseIntConst n
  Constant.Lambda (x, tx) b -> do
    defineUncurried name (Rush.Lambda (x, tx) b)
    define name $
      function
        (fromText name)
        [(asType tx, fromText x)]
        (asType $ Rush.typeOf b)
        (\[x'] -> with [(x, x')] $ ret =<< buildExpr b)

defineUncurried :: Text -> Rush.Expr Rush.Type -> ModuleBuilderT (ReaderT Vars (State BuilderState)) Operand
defineUncurried name e =
  function
    (fromText mangledName)
    argDecls
    (asType $ Rush.typeOf e)
    (\args' -> with (zip argNames args') $ ret =<< buildExpr b)
  where
    mangledName = pack $ "__" ++ unpack name
    argNames = fst <$> xs
    argTypes = asType . snd <$> xs
    argDecls = zip argTypes $ fromText <$> argNames
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
    MonadFix m,
    MonadModuleBuilder m
  ) =>
  Rush.Expr Rush.Type ->
  m Operand
buildExpr =
  deref <=< \case
    Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
    Rush.Tup xs -> error "todo"
    Rush.Var v _ -> lookup v
    Rush.Add a b -> join $ add <$> buildExpr a <*> buildExpr b
    Rush.Match xs arms -> mdo
      let xs' = (\(Rush.Var x _) -> x) <$> xs
      matchBlock <- block
      tried <- buildMatchArms returnBlock matchBlock xs' [] arms
      returnBlock <- block `named` "return"
      phi tried
    Rush.Lambda (x, _) b -> return $ parseInt "0" -- error "Lambda expressions not implemented."
    Rush.App _ f x -> do
      f' <- buildExpr f
      x <- buildExpr x
      call f' [(x, [])]

deref :: MonadIRBuilder m => Operand -> m Operand
deref op = case op of
  LocalReference PointerType {} _ -> load op 0
  _ -> return op

buildMatchArms ::
  (MonadReader Vars m, MonadState BuilderState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
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
  (MonadReader Vars m, MonadState BuilderState m, MonadIRBuilder m, MonadFix m, MonadModuleBuilder m) =>
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
      --x' <- alloca (asType (Rush.typeOfP $ Tup ps')) Nothing 0
      x' <- lookup x
      xs' <- mapM (const fresh) ps'
      --trace (show xs') return ()
      --trace (show x') return ()
      --ptr <- gep x' [int32 0]
      --trace (show ptr) return ()
      xs'' <- mapM (\(i, p') -> gep x' [int32 0, int32 i]) (zip [0 ..] ps')
      with (zip xs' xs'') $ buildMatchArm returnBlock thisBlock nextBlock (xs' ++ xs) (ps' ++ ps) e
buildMatchArm _ _ _ x p e = error $ "unreachable: buildMatchArm .. " ++ show (x, p, e)

asType :: Rush.Type -> Type
asType = \case
  Rush.TInt _ -> i64
  Rush.TTup tys -> PointerType (StructureType False $ asType <$> tys) (AddrSpace 0)
  Rush.TVar _ _ -> error "unreachable: asType TVar"
  a Rush.:-> b -> i64 -- TODO

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
