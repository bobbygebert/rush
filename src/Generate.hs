{-# LANGUAGE LambdaCase #-}

module Generate (buildModule) where

import Control.Monad.Reader (ReaderT (runReaderT))
import Control.Monad.State
import qualified Data.Map as Map
import Data.String
import Data.Text
import Data.Text.Lazy (toStrict)
import Item
import LLVM.AST
import LLVM.AST.Constant
import LLVM.AST.Type
import LLVM.IRBuilder hiding (buildModule)
import LLVM.Prelude

data BuilderState = BuilderState
  {
  }

type Builder =
  ModuleBuilderT
    (ReaderT (Map.Map String Operand) (State BuilderState))

buildModule :: String -> [Item c] -> Module
buildModule name =
  flip evalState (BuilderState {})
    . flip runReaderT Map.empty
    . buildModuleT (fromString name)
    . mapM_ buildItem

buildItem :: Item c -> Builder Operand
buildItem = \case Constant (x, _) (Num n _) _ -> global (fromText x) i64 (parseInt n)

parseInt :: Text -> Constant
parseInt = Int 64 . read . unpack

fromText :: (IsString a) => Text -> a
fromText = fromString . unpack
