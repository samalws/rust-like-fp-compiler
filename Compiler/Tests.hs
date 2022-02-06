module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheckWith, stdArgs, maxSuccess, maxSize, (==>), Property)
import Data.Either (isRight)
import Text.Parsec (parse)
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
import Compiler.Parser
import Compiler.Printer

printParseTest e = validExpr e ==> (Right e == parse exprFileParser "" (printExpr e))

betaReducePreservesWellTyped e = validExpr e ==> isRight (annotateExpr e) ==> isRight (annotateExpr $ betaReduceNormal e)

betaReduceNoLetPreservesWellTyped e = validExpr e ==> isRight (annotateExpr e) ==> isRight (annotateExpr $ betaReduce (normalBetaReduceSettings { reduceLet = False }) e)

anfIdempotent e = validExpr e ==> isRight (annotateExpr e) ==> (let e' = runAnf e in runAnf e' == e')

anfPreservesType e = validExpr e ==> isRight te ==> f te tre where
  te = exprVal <$> annotateExpr e
  tre = exprVal <$> annotateExpr (runAnf e)
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

anfPreservesEval e = validExpr e ==> isRight (annotateExpr e) ==> betaReduceNormal e == betaReduceNormal (runAnf e)

baseEvalInt e = validExpr e ==> (exprVal <$> annotateExpr e) == Right intType ==> f (betaReduceNormal e) where
  f (PrimInt _ _) = True
  f _ = False

cpsBaseEvalPreserved e = validExpr e ==> (exprVal <$> annotateExpr e) == Right intType ==> betaReduceNormal e == betaReduceNormal (app (anfWrapCps $ runAnf e) (abs' (evar 0)))

-- something kinda scary: without eliminating lets there should be a counterexample: let a = (\x. \y. 5) 6 in a a
--    but quickcheck doesn't find that counterexample at the moment
cpsPreservesWellTypedLetless e = validExpr e ==> isRight (annotateExpr e') ==> isRight (annotateExpr $ anfWrapCps $ runAnf e') where
  e' = betaReduce (normalBetaReduceSettings { reduceApp = False }) e

tests :: IO ()
tests = do
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  1000 } printParseTest
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } betaReducePreservesWellTyped
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } betaReduceNoLetPreservesWellTyped
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfIdempotent
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfPreservesType
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfPreservesEval
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } baseEvalInt
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } cpsBaseEvalPreserved
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } cpsPreservesWellTypedLetless
