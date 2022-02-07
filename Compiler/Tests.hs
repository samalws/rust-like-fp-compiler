module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheckWith, stdArgs, maxSuccess, maxSize, (==>), Property, Gen, getSize, elements, oneof, chooseInt, chooseInteger)
import Test.QuickCheck.Arbitrary.Generic (Arbitrary, arbitrary, shrink, genericArbitrary, genericShrink)
import Data.Either (isRight)
import Text.Parsec (parse)
import Control.Monad (replicateM)
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
import Compiler.Parser
import Compiler.Printer

instance Arbitrary PrimOpEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary PrimTypeEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

genArbExpr :: (Arbitrary a) => Int -> Int -> Int -> Gen (Expr a)
genArbExpr maxFn n m | m <= 0 = oneof [
    EVar <$> chooseInt (0,n-1) <*> arbitrary,
    PrimInt <$> chooseInteger (0, 99999)  <*> arbitrary,
    FnVal <$> chooseInt (0,maxFn) <*> arbitrary
  ]
genArbExpr maxFn n m = oneof [
    EVar <$> chooseInt (0,n-1) <*> arbitrary,
    App <$> gaen <*> gaen <*> arbitrary,
    Abs Nothing {- TODO -} <$> gaen1 <*> arbitrary,
    Let <$> gaen <*> gaen1 <*> arbitrary,
    PrimInt <$> arbitrary <*> arbitrary,
    (\a b -> PrimOp Plus [a,b]) <$> gaen <*> gaen <*> arbitrary,
    (\a b c -> PrimOp IfZ [a,b,c]) <$> gaen <*> gaen <*> gaen <*> arbitrary,
    chooseInt (0,4) >>= (\n -> TupAccess n <$> chooseInt (0,n-1) <*> gaen <*> arbitrary),
    chooseInt (2, min 5 m) >>= (\n -> PrimOp Tup <$> replicateM n gaen <*> arbitrary),
    FnVal <$> chooseInt (0,maxFn) <*> arbitrary
  ]
  where
    gaen  = genArbExpr maxFn n     (m-1)
    gaen1 = genArbExpr maxFn (n+1) (m-1)

typeOrderedCode' :: [Type] -> [Expr a] -> [Type]
typeOrderedCode' ts [] = ts
typeOrderedCode' ts (h:r) = typeOrderedCode' (ts <> [either (const intType) id $ exprVal <$> annotateExpr (const () <$> h)]) r

typeOrderedCode :: [Expr a] -> Code a
typeOrderedCode es = Code $ zip (typeOrderedCode' [] es) es

instance (Arbitrary a) => Arbitrary (Expr a) where
  arbitrary = getSize >>= genArbExpr (-1) 0
  shrink = genericShrink

instance Arbitrary Type where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance (Arbitrary a) => Arbitrary (Code a) where
  arbitrary = do
    size <- getSize
    numFns <- chooseInt (0,size)
    typeOrderedCode <$> mapM (\maxFn -> genArbExpr maxFn 0 size) [-1..numFns-1]
  shrink = genericShrink

printParseTest e = validExpr (-1) e ==> (Right e == parse exprFileParser "" (printExpr e))

betaReducePreservesWellTyped e = validExpr (-1) e ==> isRight (annotateExpr e) ==> isRight (annotateExpr $ betaReduceNormal e)

betaReduceNoLetPreservesWellTyped e = validExpr (-1) e ==> isRight (annotateExpr e) ==> isRight (annotateExpr $ betaReduce (normalBetaReduceSettings { reduceLet = False }) e)

anfIdempotent e = validExpr (-1) e ==> isRight (annotateExpr e) ==> (let e' = runAnf e in runAnf e' == e')

anfPreservesType e = validExpr (-1) e ==> isRight te ==> f te tre where
  te = exprVal <$> annotateExpr e
  tre = exprVal <$> annotateExpr (runAnf e)
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

anfPreservesEval e = validExpr (-1) e ==> isRight (annotateExpr e) ==> betaReduceNormal e == betaReduceNormal (runAnf e)

baseEvalInt e = validExpr (-1) e ==> (exprVal <$> annotateExpr e) == Right intType ==> f (betaReduceNormal e) where
  f (PrimInt _ _) = True
  f _ = False

cpsBaseEvalPreserved e = validExpr (-1) e ==> (exprVal <$> annotateExpr e) == Right intType ==> betaReduceNormal e == betaReduceNormal (app (anfWrapCps $ runAnf e) (abs' (evar 0)))

-- something kinda scary: without eliminating lets there should be a counterexample: let a = (\x. \y. 5) 6 in a a
--    but quickcheck doesn't find that counterexample at the moment
cpsPreservesWellTypedLetless e = validExpr (-1) e ==> isRight (annotateExpr e') ==> isRight (annotateExpr $ anfWrapCps $ runAnf e') where
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
