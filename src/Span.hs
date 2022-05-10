module Span where

import Text.Megaparsec (SourcePos (SourcePos), mkPos)

data Span = Span SourcePos SourcePos
  deriving (Show, Eq, Ord)

emptySpan :: Span
emptySpan =
  Span
    (SourcePos "" (mkPos 1) (mkPos 1))
    (SourcePos "" (mkPos 1) (mkPos 1))

span :: FilePath -> (Int, Int) -> (Int, Int) -> Span
span f (l, c) (l', c') =
  Span
    (SourcePos f (mkPos l) (mkPos c))
    (SourcePos f (mkPos l') (mkPos c'))
