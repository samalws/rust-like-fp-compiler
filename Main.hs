import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import Compiler.Types
import Compiler.HM
import Compiler.ANF
import Compiler.Parser

main = do
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e
    Right e -> do
      putStrLn "Expression parsed:"
      print e
      putStrLn "Type of expression:"
      print $ exprVal <$> annotateExpr e
      putStrLn "A-normal form:"
      print $ runAnf e
      putStrLn "Type of a-normal form:"
      print $ exprVal <$> annotateExpr (runAnf e)
