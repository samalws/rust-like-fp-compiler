{-# LANGUAGE TupleSections #-}

module Compiler.ClosureConvert where

import Prelude hiding (abs)
import Compiler.Types
import Data.Tuple.Extra ((***))
import Control.Monad.State (State, runState, modify, gets)

-- assumes each fn has 1 or more args
-- also assumes lambda lifted

closureConvertExpr :: Expr () -> Expr ()
closureConvertExpr (FnVal n ()) = primOp Tup [fnVal n, primInt 0]
closureConvertExpr (App a b ()) = app (app (tupAccess 0 2 ca) cb) (tupAccess 1 2 ca) where
  ca = closureConvertExpr a
  cb = closureConvertExpr b
closureConvertExpr (Let a b ()) = let' (closureConvertExpr a) (closureConvertExpr b)
closureConvertExpr (TupAccess n m a ()) = tupAccess n m (closureConvertExpr a)
closureConvertExpr (PrimOp op l ()) = primOp op (closureConvertExpr <$> l)
closureConvertExpr a = a

closureConvertFn' :: (Monad m) => Int -> Int -> (Expr () -> m Int) -> Expr () -> m (Expr ())
closureConvertFn' m n _ v | m == n+1 = pure newBody where
  applyAll [] v = v
  applyAll (h:t) v = applyAll t (h v)
  newBody = abs' $ abs' $ applyAll (part1 <> part2) $ let' (evar (2*n)) $ closureConvertExpr v
  part1 = replicate (n-1) $ let' $ tupAccess 0 2 $ evar 0
  part2 = (\i -> let' $ tupAccess 1 2 $ evar (2*i)) <$> [0..n-1]
closureConvertFn' m n mintFn v = do
  next <- closureConvertFn' (m+1) n mintFn v
  nextN <- mintFn next
  pure $ abs' $ abs' $ primOp Tup [fnVal nextN, primOp Tup [evar 0, evar 1]]

-- TODO we kill all the Abs type args
closureConvertFn :: (Monad m) => (Expr () -> m Int) -> Expr () -> m (Expr ())
closureConvertFn mintFn = fmap (abs' . abs' . stripAbses) . descendAbses' f where
  stripAbses (Abs _ a ()) = stripAbses a
  stripAbses a = a
  f n v = closureConvertFn' 0 n mintFn v

-- TODO breaks type signatures
closureConvertCode :: Code () -> Code ()
closureConvertCode (Code l) = Code (l' <> newFns) where
  mintFn :: Expr () -> State (Int, [Expr ()]) Int
  mintFn e = do -- NOTE: need to reverse the list at the end
    modify ((+1) *** (e:))
    gets fst
  converted = sequence $ g <$> l
  g (t,e) = (t,) <$> closureConvertFn mintFn e
  (l', (_, newFunctionsRev)) = runState converted (length l - 1, [])
  newFns = (PrimT IntT,) <$> reverse newFunctionsRev
