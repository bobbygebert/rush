import qualified BuildTest
import qualified Eval
import qualified Item
import qualified Parser
import Test.Hspec

main :: IO ()
main = hspec $ do
  Parser.spec
  Item.spec
  Eval.spec
  BuildTest.spec
