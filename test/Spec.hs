import qualified BuildTest
import qualified Eval
import qualified Parser
import Test.Hspec
import qualified Type

main :: IO ()
main = hspec $ do
  Parser.spec
  Type.spec
  Eval.spec
  BuildTest.spec
