module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheck, withMaxSuccess)
import Data.Either (isRight)
import Data.Bool.HT (implies)
import Compiler.Types
import Compiler.HM
import Compiler.ANF

anfIdempotent :: Expr () -> Bool
anfIdempotent e = validExpr e `implies` (let e' = runAnf e in runAnf e' == e')

anfStaysWellTyped :: Expr () -> Bool
anfStaysWellTyped e = ((validExpr e) && (isRight $ annotateExpr e)) `implies` (isRight $ annotateExpr $ runAnf e)

-- TODO anf preserves type

tests :: IO ()
tests = quickCheck (f anfIdempotent) >> quickCheck (f anfStaysWellTyped)   where f = withMaxSuccess 1000000
