{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}

module Generate (buildModule, spec) where

import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State
import Data.Function
import qualified Data.Map as Map
import Data.String
import Data.Text hiding (foldr)
import Data.Text.Lazy (toStrict)
import Expression
import Item
import LLVM.AST hiding (alignment, callingConvention, function, functionAttributes, metadata, returnAttributes, type')
import LLVM.AST.AddrSpace
import LLVM.AST.CallingConvention
import LLVM.AST.Constant hiding (type')
import LLVM.AST.Global (Global (Function, GlobalVariable, addrSpace, alignment, basicBlocks, callingConvention, comdat, dllStorageClass, functionAttributes, garbageCollectorName, initializer, isConstant, linkage, metadata, name, parameters, personalityFunction, prefix, returnAttributes, returnType, section, threadLocalMode, type', unnamedAddr, visibility))
import LLVM.AST.Linkage
import LLVM.AST.Type
import LLVM.AST.Typed (typeOf)
import LLVM.AST.Visibility
import LLVM.IRBuilder hiding (buildModule)
import LLVM.Prelude hiding (lookup)
import Pattern
import Test.Hspec
import Prelude hiding (lookup)

data BuilderState = BuilderState
  { globals :: Vars
  }

type Vars = Map.Map Text Operand

type Builder = ModuleBuilderT (ReaderT Vars (State BuilderState))

buildModule :: Show c => String -> [Item c] -> Module
buildModule name =
  flip evalState (BuilderState Map.empty)
    . flip runReaderT Map.empty
    . buildModuleT (fromString name)
    . mapM_ buildItem

buildItem :: Show c => Item c -> Builder Operand
buildItem = \case
  Constant (x, _) e -> define x (uncurry (global (fromText x)) =<< val)
    where
      val = case e of
        Num n _ -> return (i64, parseInt n)
        Var v _ -> do
          r <- lookup v
          let t = typeOf r
          return (t, GlobalReference t (fromText v))
  Fn (f, _) (Binding x _) b -> do
    function
      (fromText f)
      [(i64, fromText x)]
      i64
      (\[x'] -> with [(x, x')] $ ret =<< buildExpr b)

buildExpr :: (MonadReader Vars m, MonadState BuilderState m) => Expr c -> m Operand
buildExpr = \case
  Num n _ -> pure $ ConstantOperand $ parseInt n
  Var v _ -> lookup v

parseInt :: Text -> Constant
parseInt = Int 64 . read . unpack

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
    let item = Constant ("x", ()) (Num "123" ())
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
    let env = [("y", ConstantOperand (GlobalReference i64 (Name "y")))]
    let item = Constant ("x", ()) (Var "y" ())
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
                      initializer = Just (GlobalReference i64 (Name "y")),
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
    let item = Fn ("x", ()) (Binding "x" ()) (Var "x" ())
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
    let expr = Num "123" ()
    let output = (ConstantOperand (Int 64 123), [])
    runBuildExpr env expr `shouldBe` output

  it "builds var" $ do
    let env = [("x", ConstantOperand (Int 64 123))]
    let expr = Var "x" ()
    let output = (ConstantOperand (Int 64 123), [])
    runBuildExpr env expr `shouldBe` output

runBuildItem :: Show c => [(Text, Operand)] -> Item c -> (Operand, [Definition])
runBuildItem env =
  flip evalState (BuilderState Map.empty)
    . flip runReaderT (Map.fromList env)
    . runModuleBuilderT emptyModuleBuilder
    . buildItem

runBuildExpr :: Show c => [(Text, Operand)] -> Expr c -> (Operand, [Definition])
runBuildExpr env =
  flip evalState (BuilderState Map.empty)
    . flip runReaderT (Map.fromList env)
    . runModuleBuilderT emptyModuleBuilder
    . buildExpr
