{-# LANGUAGE TupleSections #-}

module Compiler.CPS where

import Prelude hiding (abs)
import Compiler.Types
import Data.Tuple.Extra ((***))
import Control.Monad.State (State, runState, modify, gets)
import Data.List.Index (indexed)
import Data.Set (toList)
import Data.Functor.Identity (Identity(..),runIdentity)

-- might produce "ill-typed" terms, if there are self-calls involved
-- "ill-typed" due to Abs arguments not being polymorphic
-- super janky example: let f = (\x. \y. 5) 6 in f f   anf preserves type, but cps breaks the type (but will still work)
-- possible fix later might be to plug in let values with differing types *before* doing cps conversion
-- TODO

anfToCpsFull :: (Monad m) => (Int -> Expr () -> m (Expr ())) -> (Expr () -> Expr () -> Expr ()) -> Expr () -> Expr () -> m (Expr ())
-- TODO r might not need to be succed
anfToCpsFull g h r (Let (App a b ()) c ()) = let' <$> (g 1 =<< anfToCpsFull g h (incVars 0 r) c) <*> pure ((incVars 0 a `app` incVars 0 b) `app` evar 0)
anfToCpsFull g h r (Let (Abs _ a ()) c ()) = let' <$> (g 2 =<< anfToCpsFull g h (evar 0) (incVars 0 a)) <*> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (Let a c ()) = let' a <$> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (App a b ()) = pure $ (a `app` b) `app` r
anfToCpsFull g h r a = pure $ h r a

anfToCps :: Expr () -> Expr () -> Expr ()
anfToCps = (runIdentity .) . anfToCpsFull ((Identity .) . repeatN abs') app where
  repeatN f 0 x = x
  repeatN f n x = repeatN f (n-1) (f x)

-- TODO this was fine to change right? where do I ever use this?
anfWrapCps :: Expr () -> Expr ()
anfWrapCps = abs' . descendAbses (anfToCps . evar)

cpsConvertCode :: Code () -> Code ()
cpsConvertCode (Code l) = Code (l' <> newFns) where
  f (t,Abs ta (Abs te x ()) ()) = (t,) <$> (abs ta . abs te . abs' <$> anfToCpsFull g h (evar 0) (incVars 0 x))
  mintFn :: Expr () -> State (Int, [Expr ()]) Int
  mintFn e = do
    modify ((+1) *** (e:))
    gets fst
  g 1 a = do
    let fv = toList $ freeVars a
    let lfv = length fv
    let mapping = [(v, tupAccess n lfv (evar 0)) | (n, v) <- indexed fv]
    let a' = replaceVars ((0,evar 1):mapping) a
    n <- mintFn (abs' $ abs' a')
    pure $ primOp Tup [fnVal n, primOp Tup $ evar <$> fv]
  h r a = (tupAccess 0 2 r `app` a) `app` tupAccess 1 2 r
  converted = sequence $ f <$> l
  (l', (_, newFunctionsRev)) = runState converted (length l - 1, [])
  newFns = (PrimT IntT,) <$> reverse newFunctionsRev
