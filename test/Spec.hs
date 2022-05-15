import qualified BuildTest
import qualified Rush.Eval as Eval
import qualified Rush.Item as Item
import qualified Rush.Parser as Parser
import Test.Hspec

main :: IO ()
main = hspec $ do
  Parser.spec
  Item.spec
  Eval.spec
  BuildTest.spec
