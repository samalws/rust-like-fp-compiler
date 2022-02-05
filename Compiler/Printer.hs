module Compiler.Printer where

import Prelude hiding (abs)
import Control.Monad.State (State, gets, modify, evalState)
import Compiler.Types

newPrinterVar :: State Int String
newPrinterVar = modify (+ 1) >> gets (("v" <>) . show)

printExpr' :: [String] -> Expr () -> State Int String
printExpr' env (EVar n ()) = pure $ env !! n
printExpr' env (App a b ()) = (\a' b' -> "(" <> a' <> ") (" <> b' <> ")") <$> printExpr' env a <*> printExpr' env b
printExpr' env (Abs Nothing a ()) = do
  v <- newPrinterVar
  (\a' -> "\\" <> v <> ". (" <> a' <> ")") <$> printExpr' (v:env) a
printExpr' env (Let a b ()) = do
  v <- newPrinterVar
  (\a' b' -> "let " <> v <> " = " <> a' <> " in " <> b') <$> printExpr' env a <*> printExpr' (v:env) b
printExpr' env (PrimInt n ()) = pure $ show n
printExpr' env (PrimOp Plus [a,b] ()) = (\a' b' -> "(" <> a' <> ") + (" <> b' <> ")") <$> printExpr' env a <*> printExpr' env b
printExpr' env (PrimOp IfZ [a,b,c] ()) = (\a' b' c' -> "ifz (" <> a' <> ") (" <> b' <> ") (" <> c' <> ")") <$> printExpr' env a <*> printExpr' env b <*> printExpr' env c
printExpr' env (PrimOp Tup l ()) = (\l' -> "(" <> f l' <> ")") <$> sequence (printExpr' env <$> l) where
  f [] = ""
  f [a] = a
  f (a:b:r) = a <> "," <> f (b:r)

printExpr :: Expr () -> String
printExpr e = evalState (printExpr' [] e) 0
