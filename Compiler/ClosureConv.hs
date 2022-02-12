module Compiler.ClosureConv where

import Prelude hiding (abs)
import Control.Monad ((>=>))
import Control.Monad.State (State, gets, modify, runState)
import Data.List.Index (indexed)
import Data.Set (toList)
import Compiler.Types

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
-- to be performed after CPS conversion
-- done in this conversion:
--   f -> (f, ())
--   a b r -> a.0 a.1 b r
--   \x. \r. y -> (f,env); emit f = \env. \x. \r. y
-- TODO add FnVal as one of the things that get anf'd
-- n0: current length of Code fns
closureConvert :: Int -> Expr () -> State [(Type, Expr ())] (Expr ())
closureConvert n0 (FnVal m ()) = pure $ primOp Tup [fnVal m, primInt 0] -- TODO replace 0 with () when void is made
closureConvert n0 (App (App a b ()) r ()) = pure $ ((tupAccess 0 2 a `app` tupAccess 1 2 a) `app` b) `app` r -- assumes that a, b, and r are alredy clean
closureConvert n0 (App _ _ ()) = error "closureConvert ran into a weird App"
closureConvert n0 (Abs t a ()) = do
  a' <- closureConvert n0 a
  (m,env) <- closureConvertEmit n0 $ abs t a'
  pure $ primOp Tup [evar m, primOp Tup $ evar <$> env]
closureConvert n0 (Let a b ()) = let' <$> closureConvert n0 a <*> closureConvert n0 b
closureConvert n0 a = pure a -- tupaccess, primop should contain only vars and ints anyway

absesTraverse :: Expr a -> (Expr a, Int)
absesTraverse (Abs _ a _) = (+1) <$> absesTraverse a
absesTraverse a = (a, 0)

-- TODO carry Abs types along
curryConvertEmits :: Int -> Expr () -> Int -> State [(Type, Expr ())] (Expr ())
curryConvertEmits n0 a 1 = pure $ abs' a
curryConvertEmits n0 a nargs | nargs < 1 = error "0 or negative number of args"
curryConvertEmits n0 a nargs = do
  e <- curryConvertEmits n0 a (nargs-1)
  m <- closureConvertEmit0 n0 e
  pure $ abs' $ fnVal m `app` evar 0

curryConvert :: Int -> Expr () -> State [(Type, Expr ())] (Expr ())
curryConvert n0 = uncurry (curryConvertEmits n0) . absesTraverse

runClosureConvert :: Code () -> Code ()
runClosureConvert (Code l) = f $ flip runState [] $ mapM ((closureConvert (length l) >=> curryConvert (length l)) . snd) l where
  f (a, s) = Code $ zip (fst <$> l) a <> reverse s
