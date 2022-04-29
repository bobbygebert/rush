{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Generate (buildModule) where

import qualified Constant
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Char
import Data.Function
import qualified Data.Map as Map
import Data.String
import Data.Text hiding (foldr, head, tail)
import Data.Text.Lazy (toStrict)
import qualified Expression as Rush
--import Item hiding (name)
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

panic :: (Monad m, MonadIRBuilder m, MonadReader Vars m, MonadState BuilderState m) => m Operand
panic = flip call [] =<< lookup "panic"

buildItem :: Constant.Named -> Builder Operand
buildItem (Constant.Named name e) = case e of
  Constant.Num n _ ->
    define name
      <$> global (fromText name) i64
      $ parseIntConst n
  Constant.Lambda (x, _) b ->
    define name $
      function
        (fromText name)
        [(i64, fromText x)]
        i64
        (\[x'] -> with [(x, x')] $ ret =<< buildExpr b)

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
  Rush.Match (Rush.Var x _) p e -> case p of
    Binding x' _ -> do
      x'' <- lookup x
      with [(x', x'')] $ buildExpr e
    Num n _ -> mdo
      let n' = parseInt n
      x' <- lookup x
      matches <- icmp EQ x' n'
      condBr matches continueB panicB
      continueB <- block `named` "continue"
      continueE <- buildExpr e
      br maybeContinue
      panicB <- block `named` "panic"
      panicE <- panic
      br maybeContinue
      maybeContinue <- block `named` "maybeContinue"
      phi [(continueE, continueB), (panicE, panicB)]
  Rush.Match {} -> error "Match on expressions not implemented."
  Rush.Lambda (x, _) b -> error "Lambda expressions not implemented."
  Rush.App _ f x -> do
    f' <- buildExpr f
    x <- buildExpr x
    call f' [(x, [])]

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
