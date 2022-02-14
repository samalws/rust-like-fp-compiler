module Compiler.ClosureConv where

import Prelude hiding (abs)
import Control.Monad ((>=>))
import Control.Monad.State (State, gets, modify, runState)
import Data.List.Index (indexed)
import Data.Set (toList)
import Data.Function.HT (nest)
import Compiler.Types
import Compiler.CPS

closureConvertEmit0 :: Int -> Expr () -> State [(Type, Expr ())] Int
closureConvertEmit0 n0 a = do
  modify ((intType, a):) -- list must be reversed once this is done; also TODO wrong type lol
  gets $ (\n -> n+n0-1) . length

closureConvertEmit :: Int -> Expr () -> State [(Type, Expr ())] (Int, [Int])
closureConvertEmit n0 a = do
  let fv = toList $ freeVars a
  let lfv = length fv
  let mapping = [(v, tupAccess n lfv (evar 0)) | (n, v) <- indexed fv]
  let a' = replaceVars mapping a
  m <- closureConvertEmit0 n0 $ abs' a'
  pure (m, fv)

-- TODO type annotations are wrong, there must be a more elegant way to do this
-- maybe push some of this back to earlier stages and uhhhhhhhhhhhhhhhhh
-- done in this conversion:
--   f -> (f, ())
--   a b r -> a.0 a.1 b r
--   \x. \r. y -> (f,env); emit f = \env. \x. \r. y
-- n0: current length of Code fns
closureConvert :: Int -> Expr () -> State [(Type, Expr ())] (Expr ())
closureConvert n0 (FnVal m ()) = pure $ primOp Tup [fnVal m, primInt 0] -- TODO replace 0 with () when void is made
closureConvert n0 (App a b ()) = pure $ (tupAccess 0 2 a `app` tupAccess 1 2 a) `app` b -- assumes that a, and b are alredy clean
closureConvert n0 (Abs t a ()) = do
  a' <- closureConvert n0 a
  (m,env) <- closureConvertEmit n0 $ abs t a'
  pure $ primOp Tup [evar m, primOp Tup $ evar <$> env]
closureConvert n0 (Let a b ()) = let' <$> closureConvert n0 a <*> closureConvert n0 b
closureConvert n0 a = pure a -- tupaccess, primop should contain only vars and ints anyway

-- gdi i really need to rename stuff
curryConvertFinalDoom :: Expr () -> Int -> Expr ()
curryConvertFinalDoom a 2 = a
curryConvertFinalDoom a 3 = a
curryConvertFinalDoom a 4 = replaceVars [(2, tupAccess 0 2 (evar 2)), (3, tupAccess 1 2 (evar 2))] a
curryConvertFinalDoom a n = let' (snd' 2) $ nest (n-5) (let' $ snd' 0) $ replaceVars ([(0, evar (n-4)), (1, evar (n-3)), (2, evar (n-2))] <> [(m, fst' (m-1)) | m <- [3..n-2]] <> [(n-1, snd' 0)]) a   where
  fst' q = tupAccess 0 2 $ evar q
  snd' q = tupAccess 1 2 $ evar q

curryConvertEmits :: Int -> Expr () -> Int -> Int -> State [(Type, Expr ())] (Expr ())
curryConvertEmits n0 a m 2 = do
  a' <- anfToCpsFull g h (evar 0) (incVars 0 a)
  pure $ abs' $ abs' $ abs' $ curryConvertFinalDoom a' m
  where
    g 1 e = closureConvert n0 $ abs' e
    h e ee = (tupAccess 0 2 e `app` tupAccess 1 2 e) `app` ee
curryConvertEmits n0 a m nargs | nargs < 1 = error "0 or negative number of args"
curryConvertEmits n0 a m nargs | m == nargs = do
  e <- curryConvertEmits n0 a m (nargs-1)
  m <- closureConvertEmit0 n0 e
  pure $ abs' $ abs' $ abs' $ evar 0 `app` primOp Tup [fnVal m, evar 1]
curryConvertEmits n0 a m nargs = do
  e <- curryConvertEmits n0 a m (nargs-1)
  m <- closureConvertEmit0 n0 e
  pure $ abs' $ abs' $ abs' $ evar 0 `app` primOp Tup [fnVal m, primOp Tup [evar 1, evar 2]]

curryConvert :: Int -> Expr () -> State [(Type, Expr ())] (Expr ())
curryConvert n0 = f . absesTraverse    where f (a,n) = curryConvertEmits n0 a n n

runClosureConvert :: Code () -> Code ()
runClosureConvert (Code l) = f $ flip runState [] $ mapM ((closureConvert (length l) >=> curryConvert (length l)) . snd) l where
  f (a, s) = Code $ zip (fst <$> l) a <> reverse s
