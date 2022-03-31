{-# LANGUAGE TupleSections #-}

module Compiler.LambdaLift where

import Prelude hiding (abs)
import Compiler.Types
import Data.Tuple.Extra ((***))
import Control.Monad.State (State, runState, modify, gets)
import Data.List.Index (indexed)
import Data.Set (toList)

-- NOTE: run BEFORE adding blank abses

-- TODO kills type info in Abses and Code

-- old fn format: \x. v
-- new fn format: \x. \env. v

lambdaLiftExpr :: (Monad m) => (Expr () -> m Int) -> Expr () -> m (Expr ())
lambdaLiftExpr mintFn (Abs t a ()) = do
  let fv = filter (/= 0) $ toList $ freeVars a
  let lfv = length fv
  let mapping = (0,evar 1):[(v, tupAccess n lfv (evar 0)) | (n, v) <- indexed fv]
  let a' = replaceVars mapping a
  a'' <- abs t . abs' <$> lambdaLiftExpr mintFn a'
  n <- mintFn a''
  pure $ primOp Tup [fnVal n, primOp Tup $ evar . (subtract 1) <$> fv]
lambdaLiftExpr mintFn (App a b ()) = do
  ca <- lambdaLiftExpr mintFn a -- TODO bad that this gets repeated?
  cb <- lambdaLiftExpr mintFn b
  pure $ (tupAccess 0 2 ca `app` cb) `app` tupAccess 1 2 ca
lambdaLiftExpr mintFn (Let a b ()) = let' <$> lambdaLiftExpr mintFn a <*> lambdaLiftExpr mintFn b
lambdaLiftExpr mintFn (TupAccess n m a ()) = tupAccess n m <$> lambdaLiftExpr mintFn a
lambdaLiftExpr mintFn (PrimOp op l ()) = primOp op <$> sequence (lambdaLiftExpr mintFn <$> l)
lambdaLiftExpr mintFn a = pure a

lambdaLiftFn :: (Monad m) => (Expr () -> m Int) -> Expr () -> m (Expr ())
lambdaLiftFn mintFn (Abs t a ()) = abs t . abs' <$> lambdaLiftExpr mintFn (incVars 0 a)

lambdaLiftCode :: Code () -> Code ()
lambdaLiftCode (Code l) = Code (l' <> newFns) where
  mintFn :: Expr () -> State (Int, [Expr ()]) Int
  mintFn e = do -- NOTE: need to reverse the list at the end
    modify ((+1) *** (e:))
    gets fst
  converted = sequence $ g <$> l
  g (t,e) = (t,) <$> lambdaLiftFn mintFn e
  (l', (_, newFunctionsRev)) = runState converted (length l - 1, [])
  newFns = (PrimT IntT,) <$> reverse newFunctionsRev
