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

anfToCpsFull :: (Monad m) => (Int -> Expr () -> m (Expr ()) -> m (Expr ())) -> (Expr () -> Expr () -> Expr ()) -> Expr () -> Expr () -> m (Expr ())
anfToCpsFull g h r (Let a@(App _ _ ()) c ()) = g 1 (incVars 0 (incVars 0 a) `app` evar 0) (anfToCpsFull g h (incVars 0 r) c)
anfToCpsFull g h r (Let a c ()) = let' a <$> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r a = pure $ h r a

-- format now: \x. \env. \r. expr
cpsConvertCode :: Code () -> Code ()
cpsConvertCode (Code l) = Code (l' <> newFns) where
  f (t,Abs ta (Abs te x ()) ()) = (t,) <$> (abs ta . abs te . abs' <$> anfToCpsFull g h (evar 0) (incVars 0 x))
  mintFn :: Expr () -> State (Int, [Expr ()]) Int
  mintFn e = do
    modify ((+1) *** (e:))
    gets fst
  -- a: function call
  -- c: stuff to run afterwards
  g 1 a c = do
    c' <- c
    let fv = filter (/= 0) $ toList $ freeVars c'
    let lfv = length fv
    let mapping = [(v, tupAccess n lfv (evar 0)) | (n, v) <- indexed fv]
    let c'' = replaceVars ((0,evar 1):mapping) c'
    n <- mintFn (abs' $ abs' c'')
    pure $ let' (primOp Tup $ evar . subtract 1 <$> fv) $ let' (primOp Tup [fnVal n, evar 0]) $ a
  h r a = (tupAccess 0 2 r `app` a) `app` tupAccess 1 2 r
  converted = sequence $ f <$> l
  (l', (_, newFunctionsRev)) = runState converted (length l - 1, [])
  newFns = (PrimT IntT,) <$> reverse newFunctionsRev
