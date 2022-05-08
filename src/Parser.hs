{-# LANGUAGE OverloadedStrings #-}

module Parser where

import qualified Ast
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Function
import qualified Data.Set as Set
import Data.Text hiding (foldl, span)
import Data.Void
import Expression
import Test.Hspec (shouldBe)
import qualified Test.Hspec as Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec
import Text.Megaparsec.Char
import Prelude hiding (span, unlines)

data Span = Span SourcePos SourcePos
  deriving (Show, Eq, Ord)

class Spanned a

emptySpan :: Span
emptySpan =
  Span
    (SourcePos "" (mkPos 1) (mkPos 1))
    (SourcePos "" (mkPos 1) (mkPos 1))

type Parser = Parsec Void Text

parseModule :: String -> Text -> Either Text [Ast.Ast Span]
parseModule path source = case result of
  Left error -> Left $ pack $ errorBundlePretty error
  Right a -> Right a
  where
    result =
      runParser
        (many ((many newline *> item) <* many newline) <* eof)
        path
        source

item :: Parser (Ast.Ast Span)
item = try constant <|> try fn <|> try ty

constant :: Parser (Ast.Ast Span)
constant = Ast.Constant <$> (spanned lowerIdent <* eq) <*> expr

fn :: Parser (Ast.Ast Span)
fn = do
  (f, s) <- lookAhead (spanned lowerIdent)
  arms <- (:) <$> arm f <*> many (try $ newline *> arm f)
  return $ Ast.Fn (f, s) arms
  where
    arm f = do
      string f *> hspace
      (,) <$> pats <*> (eq *> expr)

ty :: Parser (Ast.Ast Span)
ty = Ast.Type <$> (spanned upperIdent <* eq) <*> spanned upperIdent

pats :: Parser [Expr Span]
pats = (:) <$> atom <*> many (try (hspace *> atom))

tuple :: Parser (Expr Span)
tuple = Tup <$> parens ((:) <$> (expr <* sep) <*> (expr `sepBy1` sep))
  where
    sep = (hspace *> char ',') *> hspace

listLiteral :: Parser (Expr Span)
listLiteral = uncurry (flip List) <$> spanned (brackets (expr `sepBy` (char ',' *> hspace)))

app :: Parser (Expr Span)
app = do
  s <- getSourcePos
  (f, e) : (g, _) : fs <- ((,) <$> atom <*> getSourcePos) `sepBy1` hspace
  return $ foldl (\f (x, e) -> App (Span s e) f x) (App (Span s e) f g) fs

tag :: Parser (Expr Span)
tag = Data <$> spanned upperIdent

constructor :: Parser (Expr Span)
constructor = tag

-- TODO: Parse match expressions
expr :: Parser (Expr Span)
expr =
  makeExprParser
    term
    [ [l "*" Mul],
      [l "/" Div],
      [l "%" Mod],
      [l "+" Add],
      [l "-" Sub],
      [r "::" Cons]
    ]
  where
    l :: Text -> (Expr Span -> Expr Span -> Expr Span) -> Operator Parser (Expr Span)
    l s e = InfixL $ try (e <$ (hspace *> string s <* hspace))
    r :: Text -> (Expr Span -> Expr Span -> Expr Span) -> Operator Parser (Expr Span)
    r s e = InfixR $ try (e <$ (hspace *> string s <* hspace))

atom :: Parser (Expr Span)
atom = num <|> var <|> tag <|> listLiteral <|> try tuple <|> parens expr

term :: Parser (Expr Span)
term = try constructor <|> try app <|> atom

num :: Parser (Expr Span)
num = uncurry Num <$> spanned (pack <$> some digitChar)

var :: Parser (Expr Span)
var = uncurry Var <$> spanned lowerIdent

lowerIdent :: Parser Text
lowerIdent = pack <$> ((:) <$> lowerChar <*> many alphaNumChar)

upperIdent :: Parser Text
upperIdent = pack <$> ((:) <$> upperChar <*> many alphaNumChar)

eq :: Parser ()
eq = void (hspace *> char '=' <* hspace)

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

brackets :: Parser a -> Parser a
brackets = between (char '[') (char ']')

spanned :: Parser a -> Parser (a, Span)
spanned p = do
  s <- getSourcePos
  a <- p
  e <- getSourcePos
  return (a, Span s e)

justSpan :: Parser a -> Parser Span
justSpan = (snd <$>) . spanned

{-
 ____
/ ___| _ __   ___  ___
\___ \| '_ \ / _ \/ __|
 ___) | |_) |  __/ (__
|____/| .__/ \___|\___|
      |_|
-}

spec :: Hspec.SpecWith ()
spec = Hspec.describe "Parser" $ do
  Hspec.describe "parseModule" parseModuleSpec
  Hspec.describe "fn" fnSpec
  Hspec.describe "app" appSpec
  Hspec.describe "constant" constantSpec
  Hspec.describe "expr" exprSpec
  Hspec.describe "list" listSpec
  Hspec.describe "type" typeSpec
  Hspec.describe "lowerIdent" lowerIdentSpec
  Hspec.describe "spanned" spannedSpec

parseModuleSpec = do
  Hspec.it
    "parses module with trailing newline"
    $ parseModule testModule "x = 123\n"
      `shouldBe` Right
        [ Ast.Constant
            ("x", span (1, 1) (1, 2))
            (Num "123" (span (1, 5) (1, 8)))
        ]

fnSpec = do
  item <* eof
    & parses
      "fn with single binder"
      "f x = x"
      as
      (Ast.Fn ("f", ()) [([Var "x" ()], Var "x" ())])

  item <* eof
    & parses
      "fn with multiple parameters"
      "f x 123 = x"
      as
      (Ast.Fn ("f", ()) [([Var "x" (), Num "123" ()], Var "x" ())])

  item <* newline <* eof
    & parses
      "fn with multiple pattern branches"
      ( unlines
          [ "f 1 = 2",
            "f 2 = 3"
          ]
      )
      as
      (Ast.Fn ("f", ()) [([Num "1" ()], Num "2" ()), ([Num "2" ()], Num "3" ())])

appSpec = do
  app <* eof
    & parses
      "chained applications"
      "g x y"
      as
      (App () (App () (Var "g" ()) (Var "x" ())) (Var "y" ()))
  app <* eof
    & parses
      "application to parenthesized term"
      "g (x + x)"
      as
      (App () (Var "g" ()) (Add (Var "x" ()) (Var "x" ())))

constantSpec = do
  item <* eof
    & parses
      "constant number"
      "x = 123"
      as
      (Ast.Constant ("x", ()) (Num "123" ()))

exprSpec = do
  expr <* eof
    & parses
      "addition"
      "1 + 2"
      as
      (Add (Num "1" ()) (Num "2" ()))

listSpec = do
  expr <* eof
    & parses
      "empty list"
      "[]"
      as
      (List () [])
  expr <* eof
    & parses
      "non-empty list"
      "[1, 2]"
      as
      (List () [Num "1" (), Num "2" ()])
  expr <* eof
    & parses
      "cons list"
      "1 :: 2 :: []"
      as
      (Cons (Num "1" ()) (Cons (Num "2" ()) (List () [])))

typeSpec = do
  item <* eof
    & parses
      "marker type"
      "Marker = Marker"
      as
      (Ast.Type ("Marker", ()) ("Marker", ()))

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
