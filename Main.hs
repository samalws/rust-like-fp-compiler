import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import Compiler.Types
import Compiler.Tests
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
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
      let ee = runAnf e
      putStrLn "A-normal form:"
      print ee
      putStrLn "Type of a-normal form:"
      print $ exprVal <$> annotateExpr ee
      let eee = anfWrapCps ee
      putStrLn "CPS form:"
      print eee
      putStrLn "Type of CPS form:"
      print $ exprVal <$> annotateExpr eee
