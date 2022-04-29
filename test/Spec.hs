import qualified BuildTest
import qualified Eval
import qualified Parser
import qualified Type

main :: IO ()
main = do
  Parser.spec
  Type.spec
  Eval.spec
  BuildTest.spec
