{-# LANGUAGE TupleSections #-}

module Compiler.ClosureConvert where

import Prelude hiding (abs)
import Compiler.Types
import Data.Tuple.Extra ((***))
import Control.Monad.State (State, runState, modify, gets)
import Data.List.Index (indexed)
import Data.Set (toList)

-- NOTE: run BEFORE adding blank abses

-- TODO kills type info in Abses and Code

lambdaLiftExpr :: (Monad m) => (Expr () -> m Int) -> Expr () -> m (Expr ())
lambdaLiftExpr mintFn a@(Abs _ _ ()) = do
  let fv = toList $ freeVars a
  let lfv = length fv
  let mapping = [(v, tupAccess n lfv (evar 0)) | (n, v) <- indexed fv]
  let a' = replaceVars mapping a
  a'' <- lambdaLiftFn mintFn $ abs' a'
  n <- mintFn a''
  pure $ app (fnVal n) (primOp Tup $ evar <$> fv)
lambdaLiftExpr mintFn (App a b ()) = app <$> lambdaLiftExpr mintFn a <*> lambdaLiftExpr mintFn b
lambdaLiftExpr mintFn (Let a b ()) = let' <$> lambdaLiftExpr mintFn a <*> lambdaLiftExpr mintFn b
lambdaLiftExpr mintFn (TupAccess n m a ()) = tupAccess n m <$> lambdaLiftExpr mintFn a
lambdaLiftExpr mintFn (PrimOp op l ()) = primOp op <$> sequence (lambdaLiftExpr mintFn <$> l)
lambdaLiftExpr mintFn a = pure a

lambdaLiftFn :: (Monad m) => (Expr () -> m Int) -> Expr () -> m (Expr ())
lambdaLiftFn mintFn = descendAbses' (const $ lambdaLiftExpr mintFn)

lambdaLiftCode :: Code () -> Code ()
lambdaLiftCode (Code l) = Code (l' <> newFns) where
  -- TODO this is almost an exact copy of closureConvertCode, DRY smh
  mintFn :: Expr () -> State (Int, [Expr ()]) Int
  mintFn e = do -- NOTE: need to reverse the list at the end
    modify ((+1) *** (e:))
    gets fst
  converted = sequence $ g <$> l
  g (t,e) = (t,) <$> lambdaLiftFn mintFn e
  (l', (_, newFunctionsRev)) = runState converted (length l - 1, [])
  newFns = (PrimT IntT,) <$> reverse newFunctionsRev
