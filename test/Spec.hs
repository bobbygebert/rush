import qualified BuildTest
import qualified Generate
import qualified Parser
import qualified Type

main :: IO ()
main = do
  Parser.spec
  Type.spec
  Generate.spec
  BuildTest.spec
