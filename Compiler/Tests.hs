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

-- still doesn't pass >:C
cpsProperType :: Expr () -> Bool
cpsProperType e = (validExpr e) `implies` (f (exprVal <$> annotateExpr e) (exprVal <$> annotateExpr (anfWrapCps $ runAnf e))) where
  f (Left _) (Left _) = True
  f (Right a) (Right b) = runTypesAlphaEquiv (runTypeToCPS a) b
  f _ _ = False

tests :: IO ()
tests = f anfIdempotent >> f anfStaysWellTyped >> f anfPreservesType >> f cpsProperType   where f t = quickCheck (withMaxSuccess 1000000 t)
