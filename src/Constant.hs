module Constant (Constant (..), Named (..)) where

import Data.Text
import Expression
import Type

data Constant
  = Num Text Type
  | Lambda (Text, Type) (Expr Type)
  deriving (Show, Eq)

data Named = Named Text Constant
