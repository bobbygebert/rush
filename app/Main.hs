{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Text
import qualified Data.Text.IO as Text
import Lib
import Options.Applicative
import System.Exit (exitFailure)
import System.FilePath.Posix
import System.IO

data Command
  = Version
  | Build String
  | Check String
  deriving (Show)

main :: IO ()
main =
  getCommand >>= \case
    Version -> putStrLn "alpha"
    Build path ->
      Text.readFile path
        >>= try . build path
        >>= Text.writeFile (replaceExtension path "ll")
    Check path -> error "Not implemented"

getCommand :: IO Command
getCommand =
  execParser $
    flip info idm $
      subparser
        ( command "version" versionCommand
            <> command "build" buildCommand
            <> command "check" checkCommand
        )
        <**> helper

try :: Either [Text] ok -> IO ok
try = \case
  Left err -> const exitFailure =<< mapM (Text.hPutStrLn stderr) err
  Right ok -> pure ok

versionCommand :: ParserInfo Command
versionCommand =
  info
    (pure Version)
    (progDesc "Print rush version")

buildCommand :: ParserInfo Command
buildCommand =
  info
    (Build <$> argument str (metavar "SRC"))
    (progDesc "Build from source")

checkCommand :: ParserInfo Command
checkCommand =
  info
    (Check <$> argument str (metavar "SRC"))
    (progDesc "Check source")
