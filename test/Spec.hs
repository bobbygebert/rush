import qualified BuildTest
import qualified Rush.Eval as Eval
import qualified Rush.Infer as Infer
import qualified Rush.Parser as Parser
import Test.Hspec

main :: IO ()
main = hspec $ do
  Parser.spec
  Infer.spec
  Eval.spec
  BuildTest.spec
