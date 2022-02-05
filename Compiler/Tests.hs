module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheck, withMaxSuccess, (==>), Property)
import Data.Either (isRight)
import Compiler.Types
import Compiler.HM
import Compiler.ANF
import Compiler.CPS

anfIdempotent :: Expr () -> Property
anfIdempotent e = validExpr e ==> (let e' = runAnf e in runAnf e' == e')

anfStaysWellTyped :: Expr () -> Property
anfStaysWellTyped e = (validExpr e) ==> isRight (annotateExpr e) ==> isRight (annotateExpr (runAnf e))

anfPreservesType :: Expr () -> Property
anfPreservesType e = (validExpr e) ==> isRight te ==> f te tre where
  te = exprVal <$> annotateExpr e
  tre = exprVal <$> annotateExpr (runAnf e)
  f (Left _) (Left _) = True
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

tests :: IO ()
tests = f anfIdempotent >> f anfStaysWellTyped >> f anfPreservesType   where f t = quickCheck (withMaxSuccess 50000 t)
