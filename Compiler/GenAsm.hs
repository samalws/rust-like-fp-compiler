module Compiler.GenAsm where

import Prelude hiding (abs)
import Compiler.Types
import Compiler.RegAlloc
import Data.List.Index (indexed)
import Data.Maybe (isNothing)

asmWordSize :: Int
asmWordSize = 8

helperReg :: Register
helperReg = 100

stkPtrReg :: Register
stkPtrReg = 101

regName :: Register -> String
regName r | r == helperReg = "rax"
regName r | r == stkPtrReg = "rsp"
regName r = "r" <> show (r+8) -- using R8 thru R15

movAsm :: String -> String -> [String]
movAsm a b | a == b = []
movAsm a b = ["mov " <> a <> ", " <> b]

-- [String] is in reverse order
baseToAsm :: String -> Expr RegMap -> [String]
baseToAsm dest (EVar n regMap) = movAsm dest (regName (lookupRegMap n regMap))
baseToAsm dest (PrimInt n _) = movAsm dest (show n)
baseToAsm dest (TupAccess n _ a _) = movAsm dest ("[" <> dest <> "]") <> ["add " <> dest <> ", " <> show (n*asmWordSize)] <> baseToAsm dest a
baseToAsm dest (FnVal n _) = movAsm dest ("fn" <> show n)

letBodyToAsm :: String -> Expr RegMap -> [String]
letBodyToAsm dest (PrimOp Plus [a,b] _) = ["add " <> dest <> ", " <> regName helperReg] <> baseToAsm (regName helperReg) a <> baseToAsm dest b
letBodyToAsm dest (PrimOp IfZ [a,b,c] _) = ["cmovne " <> dest <> ", " <> regName helperReg] <> baseToAsm (regName helperReg) c <> baseToAsm dest b <> ["cmp " <> regName helperReg <> ", 0"] <> baseToAsm (regName helperReg) a
letBodyToAsm dest (PrimOp Tup l _) = movAsm dest (regName stkPtrReg) <> concat (f <$> indexed l) <> ["sub " <> regName stkPtrReg <> ", " <> show (length l * asmWordSize)] where
  f (i,x) = movAsm (regName stkPtrReg <> "[" <> show (i*asmWordSize) <> "]") (regName helperReg) <> baseToAsm (regName helperReg) x
letBodyToAsm dest a = baseToAsm dest a

fnBodyToAsm :: Expr RegMap -> [String]
fnBodyToAsm (Let a b _) | isNothing (lookupRegMapMaybe 0 $ grabRegMap b) = fnBodyToAsm b where
  grabRegMap (Let _ _ r) = r
  grabRegMap (App _ _ r) = r -- TODO DRY
fnBodyToAsm (Let a b _) = fnBodyToAsm b <> letBodyToAsm (regName $ lookupRegMap 0 $ grabRegMap b) a where
  grabRegMap (Let _ _ r) = r
  grabRegMap (App _ _ r) = r
fnBodyToAsm a@App {} = ["jmp rbx","pop rbx"] <> (g <$> indexed appVals) <> concat (f <$> reverse (fnLoc:appVals)) where
  appChainRev (App x y _) = y : appChainRev x
  appChainRev x = [x]
  (fnLoc:appVals) = reverse (appChainRev a)
  f x = ["push rbx"] <> baseToAsm "rbx" x
  g (i,x) = "pop " <> regName i


-- fnBodyToAsm a@App {} = ["jmp " <> regName 0] <> concat (f <$> indexed appVals) where
  -- f (i,x) = baseToAsm (regName i) x

fnToAsm :: Expr RegMap -> [String]
fnToAsm (Abs _ a _) = fnToAsm a
fnToAsm a = fnBodyToAsm a

codeToAsm :: Code RegMap -> String
codeToAsm (Code l) = unlines $ concat $ [startSection] <> (f <$> indexed l) <> [endSection] where
  startSection = ["section .text","global _start","_start:"] <> movAsm (regName helperReg) "finish" <> ["push " <> regName helperReg, "push " <> regName helperReg] <> movAsm (regName 2) (regName stkPtrReg) -- first? push is a dummy push
  endSection = ["finish:","mov rax, 1","mov rbx, " <> regName 0,"int 0x80"]
  f (i,(_,x)) = ("fn" <> show i <> ":") : reverse (fnToAsm x)
