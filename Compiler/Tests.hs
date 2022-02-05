module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheck, withMaxSuccess, (==>), Property)
import Data.Either (isRight)
import Text.Parsec (parse)
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
import Compiler.Parser
import Compiler.Printer

fnPreservesWellTyped :: (Expr () -> Expr ()) -> Expr () -> Property
fnPreservesWellTyped g e = validExpr e ==> isRight (annotateExpr e) ==> isRight (annotateExpr $ g e)

fnPreservesType :: (Expr () -> Expr ()) -> Expr () -> Property
fnPreservesType g e = validExpr e ==> isRight te ==> f te tre where
  te = exprVal <$> annotateExpr e
  tre = exprVal <$> annotateExpr (g e)
  f (Left _) (Left _) = True
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

fnPreservesEval :: (Expr () -> Expr ()) -> Expr () -> Property
fnPreservesEval g e = validExpr e ==> isRight (annotateExpr e) ==> betaReduce e == betaReduce (g e)

fnIdempotent :: (Expr () -> Expr ()) -> Expr () -> Property
fnIdempotent g e = validExpr e ==> isRight (annotateExpr e) ==> (let e' = g e in g e' == e')

printParseTest :: Expr () -> Property
printParseTest e = validExpr e ==> (Right e == (parse exprFileParser "" $ printExpr e))

tests :: IO ()
tests = do
  quickCheck $ withMaxSuccess  1000 $ printParseTest
  quickCheck $ withMaxSuccess 50000 $ fnPreservesWellTyped betaReduce
  quickCheck $ withMaxSuccess 50000 $ fnIdempotent runAnf
  quickCheck $ withMaxSuccess 50000 $ fnPreservesType runAnf
  quickCheck $ withMaxSuccess 50000 $ fnPreservesEval runAnf
