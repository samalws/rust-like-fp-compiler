import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.LambdaLift
import Compiler.AddBlankAbses
import Compiler.ClosureConvert
import Compiler.ANF
import Compiler.CPS
import Compiler.RegSpill
import Compiler.RegAlloc
import Compiler.GenAsm
import Compiler.Parser
import Compiler.Printer
import Compiler.Tests

main = do
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e
    Right e -> do
      let c = Code [(PrimT IntT, e)]
      print $ regAllocCode . regSpillCode 7 . cpsConvertCode . anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      let c' = regSpillCode 7 . cpsConvertCode . anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      let asm = codeToAsm . regAllocCode $ c'
      writeFile "otp.asm" asm
