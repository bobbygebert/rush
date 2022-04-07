import qualified BuildTest
import qualified Generate
import qualified Parser

main :: IO ()
main = do
  Parser.spec
  Generate.spec
  BuildTest.spec
