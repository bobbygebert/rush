import qualified BuildTest
import qualified Parser
import qualified Type

main :: IO ()
main = do
  Parser.spec
  Type.spec
  BuildTest.spec
