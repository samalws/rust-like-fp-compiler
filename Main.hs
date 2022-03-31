import Prelude hiding (abs)
import Text.Parsec
import Text.Parsec.String
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
import Compiler.Tests

main = do
  contents <- parseFromFile exprFileParser "input.txt"
  case contents of
    Left e -> print e
    Right e -> do
      let c = Code [(PrimT IntT, e)]
      putStrLn $ printCode $ addBlankAbses $ c
      putStrLn $ printCode $ lambdaLiftCode . addBlankAbses $ c
      putStrLn $ printCode $ anfCode . lambdaLiftCode . addBlankAbses $ c
      putStrLn $ printCode $ cpsConvertCode . anfCode . lambdaLiftCode . addBlankAbses $ c
      putStrLn $ printCode $ regSpillCode 7 . cpsConvertCode . anfCode . lambdaLiftCode . addBlankAbses $ c
      let c' = regSpillCode 7 . cpsConvertCode . anfCode . lambdaLiftCode . addBlankAbses $ c
      let asm = codeToAsm . regAllocCode $ c'
      writeFile "otp.asm" asm




{-
      putStrLn "original code:"
      print c
      putStrLn "lambda lifted, blank functions given dummy arguments:"
      print $ addBlankAbses . lambdaLiftCode $ c
      putStrLn "closure converted:"
      print $ closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      putStrLn "ANF:"
      print $ anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      putStrLn "CPS:"
      print $ cpsConvertCode . anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      putStrLn "register spilled:"
      print $ regSpillCode 7 . cpsConvertCode . anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
      putStrLn "registers allocated:"
      print $ regAllocCode . regSpillCode 7 . cpsConvertCode . anfCode . closureConvertCode . addBlankAbses . lambdaLiftCode $ c
-}
