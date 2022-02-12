import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.AddBlankAbses
import Compiler.ANF
import Compiler.CPS
import Compiler.ClosureConv
import Compiler.RegSpill
import Compiler.RegAlloc
import Compiler.Parser
import Compiler.Printer
import Compiler.Tests

main = do
  tests
  {-
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e
    Right e -> do
      putStrLn "Expression parsed:"
      print e
      putStrLn $ printExpr e
      putStrLn "Type of expression:"
      print $ exprVal <$> annotateExpr [] e
      let ee = runAnf e
      putStrLn "A-normal form:"
      putStrLn $ printExpr ee
      putStrLn "Type of a-normal form:"
      print $ exprVal <$> annotateExpr [] ee
      let eee = anfWrapCps ee
      putStrLn "CPS form:"
      putStrLn $ printExpr eee
      putStrLn "Type of CPS form:"
      print $ exprVal <$> annotateExpr [] eee
      let eeee = regSpill 4 ee
      putStrLn "Register spilled (from ANF) (r=4):"
      putStrLn $ printExpr eeee
      let eeeee = runRegAlloc ee
      putStrLn "Register alloced (from ANF) (r=4):"
      print eeeee
      putStrLn "Original beta reduced:"
      putStrLn $ printExpr $ betaReduceNormal e
      putStrLn "ANF beta reduced:"
      putStrLn $ printExpr $ betaReduceNormal ee
      putStrLn "CPS beta reduced:"
      putStrLn $ printExpr $ betaReduceNormal $ app eee (abs' (evar 0))
  -}
