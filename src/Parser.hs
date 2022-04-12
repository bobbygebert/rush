{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Ast
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Function
import qualified Data.Set as Set
import Data.Text hiding (span)
import Data.Void
import Expression
import qualified Pattern
import Test.Hspec (shouldBe)
import qualified Test.Hspec as Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec
import Text.Megaparsec.Char
import Prelude hiding (span)

data Span = Span SourcePos SourcePos
  deriving (Show, Eq)

type Parser = Parsec Void Text

parseModule :: String -> Text -> Either Text [Ast Span]
parseModule path source = case result of
  Left error -> Left $ pack $ errorBundlePretty error
  Right a -> Right a
  where
    result =
      runParser
        (many ((many newline *> item) <* many newline) <* eof)
        path
        source

item :: Parser (Ast Span)
item = try constant <|> try fn

constant :: Parser (Ast Span)
constant = Constant <$> (spanned lowerIdent <* eq) <*> expr

fn :: Parser (Ast Span)
fn = Fn <$> spanned lowerIdent <*> (hspace *> pat) <*> (eq *> expr)

pat :: Parser (Pattern.Pattern Span)
pat = binding <|> numPat

binding :: Parser (Pattern.Pattern Span)
binding = uncurry Pattern.Binding <$> spanned lowerIdent

numPat :: Parser (Pattern.Pattern Span)
numPat = uncurry Pattern.Num <$> spanned (pack <$> some digitChar)

-- TODO: Parse match expressions
expr :: Parser (Expr Span)
expr =
  makeExprParser
    term
    [ [binary "+" Add]
    ]
  where
    binary :: Text -> (Expr Span -> Expr Span -> Expr Span) -> Operator Parser (Expr Span)
    binary s e = InfixL (e <$ (hspace *> string s <* hspace))

term :: Parser (Expr Span)
term = choice [atom]

atom :: Parser (Expr Span)
atom = num <|> var

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
  Hspec.describe "pat" patSpec
  Hspec.describe "constant" constantSpec
  Hspec.describe "expr" exprSpec
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
  item <* eof
    & parses
      "fn with single binder"
      "f x = x"
      as
      (Fn ("f", ()) (Pattern.Binding "x" ()) (Var "x" ()))

patSpec = do
  pat <* eof
    & parses
      "binder pattern"
      "x"
      as
      (Pattern.Binding "x" ())

  pat <* eof
    & parses
      "num pattern"
      "123"
      as
      (Pattern.Num "123" ())

constantSpec = do
  item <* eof
    & parses
      "constant number"
      "x = 123"
      as
      (Constant ("x", ()) (Num "123" ()))

exprSpec = do
  expr <* eof
    & parses
      "addition"
      "1 + 2"
      as
      (Add (Num "1" ()) (Num "2" ()))

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
