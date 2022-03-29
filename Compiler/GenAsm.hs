module Compiler.GenAsm where

import Prelude hiding (abs)
import Compiler.Types
import Compiler.RegAlloc
import Data.List.Index (indexed)

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

movAsm :: String -> String -> String
movAsm a b = "mov " <> a <> ", " <> b

-- [String] is in reverse order
baseToAsm :: String -> Expr RegMap -> [String]
baseToAsm dest (EVar n regMap) = [movAsm dest (regName (lookupRegMap n regMap))]
baseToAsm dest (PrimInt n _) = [movAsm dest (show n)]
baseToAsm dest (TupAccess n _ a _) = [movAsm dest (dest <> "[" <> show n <> "]")] <> baseToAsm dest a
baseToAsm dest (FnVal n _) = [movAsm dest ("fn" <> (show n))]

letBodyToAsm :: String -> Expr RegMap -> [String]
letBodyToAsm dest (PrimOp Plus [a,b] _) = ["add " <> dest <> ", " <> (regName helperReg)] <> baseToAsm (regName helperReg) a <> baseToAsm dest b
letBodyToAsm dest (PrimOp Tup l _) = ["add " <> (regName stkPtrReg) <> ", " <> show (length l * asmWordSize), movAsm dest (regName stkPtrReg)] <> concat (f <$> indexed l) where
  f (i,x) = baseToAsm (regName stkPtrReg <> "[" <> show (i*asmWordSize) <> "]") x
letBodyToAsm dest a = baseToAsm dest a

fnBodyToAsm :: Expr RegMap -> [String]
fnBodyToAsm (Let a b _) = fnBodyToAsm b <> letBodyToAsm (regName $ lookupRegMap 0 $ grabRegMap b) a where
  grabRegMap (Let _ _ r) = r
  grabRegMap (App _ _ r) = r
fnBodyToAsm a@(App _ _ _) = ["jmp " <> (regName 0)] <> concat (f <$> indexed appVals) where
  appChainRev (App x y _) = y : (appChainRev x)
  appChainRev x = [x]
  appVals = reverse (appChainRev a)
  f (i,x) = baseToAsm (regName i) x

fnToAsm :: Expr RegMap -> [String]
fnToAsm (Abs _ a _) = fnToAsm a
fnToAsm a = fnBodyToAsm a

codeToAsm :: Code RegMap -> String
codeToAsm (Code l) = unlines $ concat $ [startSection] <> (f <$> indexed l) <> [endSection] where
  startSection = ["section .text","global start","start:",movAsm (regName 2) "finish"]
  endSection = ["finish:","mov rsp, " <> (regName 1),"mov rax, 4","mov rbx, 1","mov rcx, rsp","mov rdx, 1","int 0x80","mov rax, 1","mov rbx, 0","int 0x80"]
  f (i,(_,x)) = ("fn" <> show i <> ":"):(reverse $ fnToAsm x)