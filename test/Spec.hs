import qualified BuildTest
import qualified Parser

main :: IO ()
main = do
  BuildTest.spec
  Parser.spec
