module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheck, withMaxSuccess)
import Data.Either (isRight)
import Data.Bool.HT (implies)
import Compiler.Types
import Compiler.HM
import Compiler.ANF
import Compiler.CPS

anfIdempotent :: Expr () -> Bool
anfIdempotent e = validExpr e `implies` (let e' = runAnf e in runAnf e' == e')

anfStaysWellTyped :: Expr () -> Bool
anfStaysWellTyped e = ((validExpr e) && (isRight $ annotateExpr e)) `implies` (isRight $ annotateExpr $ runAnf e)

anfPreservesType :: Expr () -> Bool
anfPreservesType e = (validExpr e) `implies` (f (exprVal <$> annotateExpr e) (exprVal <$> annotateExpr (runAnf e))) where
  f (Left _) (Left _) = True
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

{-
-- TODO:
--   need to have a version of Plus that's in CPS
--   need to have a way to convert types before CPS to types after, since basically every function's type gets clobbered
cpsProperType :: Expr () -> Bool
cpsProperType e = (validExpr e) `implies` (f (exprVal <$> annotateExpr e) (exprVal <$> annotateExpr (anfWrapCps $ runAnf e))) where
  f (Left _) (Left _) = True
  f (Right a) (Right b) = runTypesAlphaEquiv ((a `Fn` t) `Fn` t) b where t = TVar $ highestTypeVar a + 1
  f _ _ = False
-}

tests :: IO ()
tests = f anfIdempotent >> f anfStaysWellTyped >> f anfPreservesType   where f t = quickCheck (withMaxSuccess 1000000 t)
