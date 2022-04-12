{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Generate (buildModule, spec) where

import Ast
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Char
import Data.Function
import qualified Data.Map as Map
import Data.String
import Data.Text hiding (foldr, head, tail)
import Data.Text.Lazy (toStrict)
import qualified Expression as Rush
import LLVM.AST hiding (Add, alignment, callingConvention, function, functionAttributes, metadata, returnAttributes, type')
import LLVM.AST.AddrSpace
import LLVM.AST.CallingConvention
import LLVM.AST.Constant (Constant (Add))
import LLVM.AST.Constant hiding (Add, type')
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

buildModule :: Show c => String -> [Ast c] -> Module
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

buildItem :: Show c => Ast c -> Builder Operand
buildItem = \case
  Constant (x, _) e -> define x (uncurry (global (fromText x)) =<< val)
    where
      val = case e of
        Rush.Num n _ -> return (i64, parseIntConst n)
        Rush.Var v _ -> do
          r <- lookupConst v
          let t = typeOf r
          return (t, r)
        Rush.Add a b -> do
          a' <- buildConstExpr a
          b' <- buildConstExpr b
          return (i64, Add True True a' b')
  Fn (f, _) (Binding x _) b -> do
    function
      (fromText f)
      [(i64, fromText x)]
      i64
      (\[x'] -> with [(x, x')] $ ret =<< buildExpr b)
  Fn (f, _) (Num n _) b -> do
    x <- fresh
    let n' = parseInt n
    function
      (fromText f)
      [(i64, fromText x)]
      i64
      ( \[x'] -> with [(x, x')] $ mdo
          matches <- icmp EQ x' n'
          -- TODO: use `switch` instead
          condBr matches continueB panicB
          continueB <- block `named` "continue"
          continueE <- buildExpr b
          br maybeContinue
          panicB <- block `named` "panic"
          panicE <- panic
          br maybeContinue
          maybeContinue <- block `named` "maybeContinue"
          ret =<< phi [(continueE, continueB), (panicE, panicB)]
      )

buildExpr :: (MonadReader Vars m, MonadState BuilderState m) => Rush.Expr c -> m Operand
buildExpr = \case
  Rush.Num n _ -> pure $ ConstantOperand $ parseIntConst n
  Rush.Var v _ -> lookup v
  _ -> error ""

buildConstExpr :: (MonadReader Vars m, MonadState BuilderState m) => Rush.Expr c -> m Constant
buildConstExpr = \case
  Rush.Num n _ -> pure $ parseIntConst n
  Rush.Var v _ -> lookupConst v
  _ -> error ""

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
    err = unpack name ++ "not found"
    global = gets $ Map.lookup name . globals
    local = asks $ Map.lookup name

lookupConst :: (MonadReader Vars m, MonadState BuilderState m) => Text -> m Constant
lookupConst name =
  toConst <$> (fromMaybe <$> (fromMaybe (error err) <$> global) <*> local)
  where
    err = unpack name ++ "not found"
    global = gets $ Map.lookup name . globals
    local = asks $ Map.lookup name
    toConst = \case
      (ConstantOperand c) -> c
      _ -> error "Unreachable"

define :: (MonadState BuilderState m) => Text -> m Operand -> m Operand
define name op = do
  op <- op
  state <- get
  put (state {globals = Map.insert name op (globals state)})
  pure op

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: IO ()
spec = hspec $ do
  describe "buildItem" buildItemSpec
  describe "buildExpr" buildExprSpec

buildItemSpec = do
  it "builds constant num" $ do
    let env = []
    let item = Constant ("x", ()) (Rush.Num "123" ())
    let output =
          ( ConstantOperand
              (GlobalReference (PointerType i64 (AddrSpace 0)) (Name "x")),
            [ GlobalDefinition
                ( GlobalVariable
                    { name = Name "x",
                      linkage = External,
                      visibility = Default,
                      dllStorageClass = Nothing,
                      threadLocalMode = Nothing,
                      unnamedAddr = Nothing,
                      isConstant = False,
                      addrSpace = AddrSpace 0,
                      initializer = Just (Int 64 123),
                      section = Nothing,
                      comdat = Nothing,
                      type' = i64,
                      metadata = [],
                      alignment = 0
                    }
                )
            ]
          )
    runBuildItem env item `shouldBe` output

  it "builds constant ref" $ do
    let env = [("y", ConstantOperand (Int 64 123))]
    let item = Constant ("x", ()) (Rush.Var "y" ())
    let output =
          ( ConstantOperand
              (GlobalReference (PointerType i64 (AddrSpace 0)) (Name "x")),
            [ GlobalDefinition
                ( GlobalVariable
                    { name = Name "x",
                      linkage = External,
                      visibility = Default,
                      dllStorageClass = Nothing,
                      threadLocalMode = Nothing,
                      unnamedAddr = Nothing,
                      isConstant = False,
                      addrSpace = AddrSpace 0,
                      initializer = Just (Int 64 123),
                      section = Nothing,
                      comdat = Nothing,
                      type' = i64,
                      metadata = [],
                      alignment = 0
                    }
                )
            ]
          )
    runBuildItem env item `shouldBe` output

  it "builds constant expr" $ do
    let env = []
    let item = Constant ("x", ()) (Rush.Add (Rush.Num "1" ()) (Rush.Num "2" ()))
    let output =
          ( ConstantOperand
              (GlobalReference (PointerType i64 (AddrSpace 0)) (Name "x")),
            [ GlobalDefinition
                ( GlobalVariable
                    { name = Name "x",
                      linkage = External,
                      visibility = Default,
                      dllStorageClass = Nothing,
                      threadLocalMode = Nothing,
                      unnamedAddr = Nothing,
                      isConstant = False,
                      addrSpace = AddrSpace 0,
                      initializer = Just (Add True True (Int 64 1) (Int 64 2)),
                      section = Nothing,
                      comdat = Nothing,
                      type' = i64,
                      metadata = [],
                      alignment = 0
                    }
                )
            ]
          )
    runBuildItem env item `shouldBe` output

  it "builds fn" $ do
    let env = []
    let item = Fn ("x", ()) (Binding "x" ()) (Rush.Var "x" ())
    let output =
          ( ConstantOperand
              ( GlobalReference
                  ( PointerType
                      FunctionType
                        { resultType = i64,
                          argumentTypes = [i64],
                          isVarArg = False
                        }
                      (AddrSpace 0)
                  )
                  (Name "x")
              ),
            [ GlobalDefinition
                ( Function
                    { linkage = External,
                      visibility = Default,
                      dllStorageClass = Nothing,
                      callingConvention = C,
                      returnAttributes = [],
                      returnType = i64,
                      name = Name "x",
                      parameters = ([Parameter i64 (Name "x_0") []], False),
                      functionAttributes = [],
                      section = Nothing,
                      comdat = Nothing,
                      alignment = 0,
                      garbageCollectorName = Nothing,
                      prefix = Nothing,
                      basicBlocks =
                        [ BasicBlock
                            (UnName 0)
                            []
                            ( Do
                                ( Ret
                                    { returnOperand = Just (LocalReference i64 (Name "x_0")),
                                      metadata' = []
                                    }
                                )
                            )
                        ],
                      personalityFunction = Nothing,
                      metadata = []
                    }
                )
            ]
          )
    runBuildItem env item `shouldBe` output

buildExprSpec = do
  it "builds number" $ do
    let env = []
    let expr = Rush.Num "123" ()
    let output = (ConstantOperand (Int 64 123), [])
    runBuildExpr env expr `shouldBe` output

  it "builds var" $ do
    let env = [("x", ConstantOperand (Int 64 123))]
    let expr = Rush.Var "x" ()
    let output = (ConstantOperand (Int 64 123), [])
    runBuildExpr env expr `shouldBe` output

runBuildItem :: Show c => [(Text, Operand)] -> Ast c -> (Operand, [Definition])
runBuildItem env =
  flip evalState (BuilderState Map.empty freshNames)
    . flip runReaderT (Map.fromList env)
    . runModuleBuilderT emptyModuleBuilder
    . buildItem

runBuildExpr :: Show c => [(Text, Operand)] -> Rush.Expr c -> (Operand, [Definition])
runBuildExpr env =
  flip evalState (BuilderState Map.empty freshNames)
    . flip runReaderT (Map.fromList env)
    . runModuleBuilderT emptyModuleBuilder
    . buildExpr
