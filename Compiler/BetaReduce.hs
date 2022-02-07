module Compiler.BetaReduce where

import Prelude hiding (abs)
import Compiler.Types

-- TODO setting on whether to reduce fully or not
data BetaReduceSettings = BetaReduceSettings { enterAbs :: Bool, reduceLet :: Bool, reduceApp :: Bool, reduceIfVals :: Bool, betaReduceFns :: [Expr ()] }
normalBetaReduceSettings = BetaReduceSettings True True True False []
fullBetaReduceSettings = BetaReduceSettings True True True True []

betaReduce :: BetaReduceSettings -> Expr () -> Expr ()
betaReduce set (App (Abs _ a ()) b ()) | reduceApp set = betaReduce set $ replaceVar 0 (betaReduce set b) a
betaReduce set (App a b ()) = f $ app a' b' where
  a' = betaReduce set a
  b' = betaReduce set b
  anythingChanged = a' /= a || b' /= b
  f = if anythingChanged then betaReduce set else id
betaReduce set (Abs t a ()) | enterAbs set = abs t $ betaReduce set a
betaReduce set (Let a b ()) | reduceLet set = betaReduce set $ replaceVar 0 (betaReduce set a) b
betaReduce set (Let a b ()) | not (reduceLet set) = let' (betaReduce set a) (betaReduce set b)
betaReduce set (PrimOp Plus [PrimInt n (), PrimInt m ()] ()) = primInt (n+m)
betaReduce set (PrimOp Plus [n, m] ()) = (if anythingChanged then betaReduce set else id) (primOp Plus [n', m']) where
  n' = betaReduce set n
  m' = betaReduce set m
  anythingChanged = n' /= n || m' /= m
betaReduce set (TupAccess n m (PrimOp Tup l ()) ()) | length l == m = betaReduce set (l !! n)
betaReduce set (TupAccess n m a ()) = (if anythingChanged then betaReduce set else id) (tupAccess n m a') where
  a' = betaReduce set a
  anythingChanged = a' /= a
betaReduce set (PrimOp IfZ [PrimInt n (), a, b] ()) = betaReduce set $ if n == 0 then a else b
betaReduce set (PrimOp IfZ [n, a, b] ()) = (if nChanged then betaReduce set else id) (primOp IfZ [n', f a, f b]) where
  f = if reduceIfVals set then betaReduce set else id
  n' = betaReduce set n
  nChanged = n' /= n
betaReduce set (PrimOp Tup l ()) = primOp Tup (betaReduce set <$> l)
betaReduce set (FnVal m ()) | m < length (betaReduceFns set) = betaReduceFns set !! m
betaReduce set a = a

betaReduceNormal = betaReduce normalBetaReduceSettings
betaReduceFull = betaReduce fullBetaReduceSettings
