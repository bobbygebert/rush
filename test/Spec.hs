import qualified BuildTest
import qualified Eval
import qualified Parser
import qualified Type

import Test.Hspec

main :: IO ()
main = hspec $ do
  Parser.spec
  Type.spec
  Eval.spec
  BuildTest.spec
