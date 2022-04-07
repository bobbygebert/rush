{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Monad
import Data.Function
import Data.Text hiding (span)
import Data.Void
import Expression
import Item
import Pattern
import Test.Hspec (shouldBe)
import qualified Test.Hspec as Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec
import Text.Megaparsec.Char
import Prelude hiding (span)

data Span = Span SourcePos SourcePos
  deriving (Show, Eq)

type Parser = Parsec Void Text

parseModule :: String -> Text -> Either Text [Item Span]
parseModule path source = case result of
  Left error -> Left $ pack $ errorBundlePretty error
  Right a -> Right a
  where
    result =
      runParser
        (many ((many newline *> item) <* many newline) <* eof)
        path
        source

item :: Parser (Item Span)
item = try constant <|> try fn

constant :: Parser (Item Span)
constant = Constant <$> (spanned lowerIdent <* eq) <*> expr

fn :: Parser (Item Span)
fn = Fn <$> spanned lowerIdent <*> (hspace *> pat) <*> (eq *> expr)

pat :: Parser (Pattern Span)
pat = uncurry Binding <$> spanned lowerIdent

expr :: Parser (Expr Span)
expr = num <|> var

num :: Parser (Expr Span)
num = uncurry Num <$> spanned (pack <$> some digitChar)

var :: Parser (Expr Span)
var = uncurry Var <$> spanned lowerIdent

lowerIdent :: Parser Text
lowerIdent = pack <$> ((:) <$> lowerChar <*> many alphaNumChar)

eq :: Parser ()
eq = void (hspace *> char '=' <* hspace)

spanned :: Parser a -> Parser (a, Span)
spanned p = do
  s <- getSourcePos
  a <- p
  e <- getSourcePos
  return (a, Span s e)

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: IO ()
spec = Hspec.hspec $ do
  Hspec.describe "parseModule" parseModuleSpec
  Hspec.describe "fn" fnSpec
  Hspec.describe "constant" constantSpec
  Hspec.describe "lowerIdent" lowerIdentSpec
  Hspec.describe "spanned" spannedSpec

parseModuleSpec = do
  Hspec.it
    "parses module with trailing newline"
    $ parseModule testModule "x = 123\n"
      `shouldBe` Right
        [ Constant
            ("x", span (1, 1) (1, 2))
            (Num "123" (span (1, 5) (1, 8)))
        ]

fnSpec = do
  item
    & parses
      "fn with single binder"
      "f x = x"
      as
      (Fn ("f", ()) (Binding "x" ()) (Var "x" ()))

constantSpec = do
  item
    & parses
      "constant number"
      "x = 123"
      as
      (Constant ("x", ()) (Num "123" ()))

lowerIdentSpec =
  Hspec.it
    "parses identifiers"
    (parse lowerIdent "" "aBc123" `shouldParse` "aBc123")

spannedSpec =
  Hspec.it
    "parses spanned inner"
    $ parse (spanned lowerIdent) testModule "abc" `shouldParse` ("abc", span (1, 1) (1, 4))

plain :: Functor m => m c -> m ()
plain = void

data As = As

as = As

testModule = "Lib.rush"

span (l, c) (l', c') =
  Span
    (SourcePos testModule (mkPos l) (mkPos c))
    (SourcePos testModule (mkPos l') (mkPos c'))

parses description input As expected parser =
  Hspec.it
    ("parses " ++ description)
    $ (plain <$> parse parser testModule input) `shouldParse` expected
