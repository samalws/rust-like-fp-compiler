import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
import Compiler.Parser
import Compiler.Printer
import Compiler.Tests

main = do
  tests
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e
    Right e -> do
      putStrLn "Expression parsed:"
      print e
      putStrLn "Type of expression:"
      print $ exprVal <$> annotateExpr [] e
      let ee = runAnf e
      putStrLn "A-normal form:"
      print ee
      putStrLn "Type of a-normal form:"
      print $ exprVal <$> annotateExpr [] ee
      let eee = anfWrapCps ee
      putStrLn "CPS form:"
      print eee
      putStrLn "Type of CPS form:"
      print $ exprVal <$> annotateExpr [] eee
      putStrLn "Original beta reduced:"
      print $ betaReduceNormal e
      putStrLn "ANF beta reduced:"
      print $ betaReduceNormal ee
      putStrLn "CPS beta reduced:"
      print $ betaReduceNormal $ app eee (abs' (evar 0))
