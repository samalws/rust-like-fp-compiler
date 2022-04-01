import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import System.Exit (exitFailure)
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.LambdaLift
import Compiler.AddBlankAbses
import Compiler.ANF
import Compiler.CPS
import Compiler.RegSpill
import Compiler.RegAlloc
import Compiler.GenAsm
import Compiler.Parser
import Compiler.Printer
-- import Compiler.Tests

main = do
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e >> exitFailure
    Right e -> do
      case (annotateExpr [] e) of
        Left e' -> print e' >> exitFailure
        Right _ -> do
          let c = Code [(PrimT IntT, e)]
          let c' = regSpillCode 7 . cpsConvertCode . anfCode . lambdaLiftCode . addBlankAbses $ c
          let asm = codeToAsm . regAllocCode $ c'
          writeFile "otp.asm" asm
