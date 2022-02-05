module Compiler.BetaReduce where

import Prelude hiding (abs)
import Compiler.Types

betaReduce :: Expr () -> Expr ()
betaReduce (App (Abs _ a ()) b ()) = betaReduce $ replaceVar 0 (betaReduce b) a
betaReduce (App a b ()) = (if anythingChanged then betaReduce else id) (app a' b') where
  a' = betaReduce a
  b' = betaReduce b
  anythingChanged = a' /= a || b' /= b
betaReduce (Abs t a ()) = abs t $ betaReduce a
betaReduce (Let a b ()) = betaReduce $ replaceVar 0 (betaReduce a) b
betaReduce (PrimOp Plus [PrimInt n (), PrimInt m ()] ()) = primInt (n+m)
betaReduce (PrimOp Plus [n, m] ()) = (if anythingChanged then betaReduce else id) (primOp Plus [n', m']) where
  n' = betaReduce n
  m' = betaReduce m
  anythingChanged = n' /= n || m' /= m
betaReduce (PrimOp IfZ [PrimInt n (), a, b] ()) = betaReduce $ if n == 0 then a else b
betaReduce (PrimOp IfZ [n, a, b] ()) = (if nChanged then betaReduce else id) (primOp IfZ [n', betaReduce a, betaReduce b]) where
  n' = betaReduce n
  nChanged = n' /= n
betaReduce (PrimOp Tup l ()) = primOp Tup (betaReduce <$> l)
betaReduce a = a
