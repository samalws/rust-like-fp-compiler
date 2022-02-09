module Compiler.Tests where

import Prelude hiding (abs)
import Test.QuickCheck (quickCheckWith, stdArgs, maxSuccess, maxSize, (==>), Property, Gen, getSize, elements, oneof, chooseInt, chooseInteger, shuffle)
import Test.QuickCheck.Arbitrary.Generic (Arbitrary, arbitrary, shrink, genericArbitrary, genericShrink)
import Data.Either (isRight, fromRight)
import Data.Tuple.Extra (second)
import Text.Parsec (parse)
import Control.Monad (replicateM, void)
import Compiler.Types
import Compiler.BetaReduce
import Compiler.HM
import Compiler.ANF
import Compiler.CPS
import Compiler.RegSpill
import Compiler.RegAlloc
import Compiler.Parser
import Compiler.Printer

instance Arbitrary PrimOpEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary PrimTypeEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

optFnList :: (Arbitrary a) => Int -> [Gen (Expr a)]
optFnList (-1) = []
optFnList maxFn = [FnVal <$> chooseInt (0, maxFn) <*> arbitrary]

genArbExpr :: (Arbitrary a) => Int -> Int -> Int -> Gen (Expr a)
genArbExpr maxFn n m | m <= 0 = oneof $ optFnList maxFn <> [
    EVar <$> chooseInt (0,n-1) <*> arbitrary,
    PrimInt <$> chooseInteger (0, 99999)  <*> arbitrary
  ]
genArbExpr maxFn n m = oneof $ optFnList maxFn <> [
    EVar <$> chooseInt (0,n-1) <*> arbitrary,
    App <$> gaen <*> gaen <*> arbitrary,
    Abs Nothing {- TODO -} <$> gaen1 <*> arbitrary,
    Let <$> gaen <*> gaen1 <*> arbitrary,
    PrimInt <$> arbitrary <*> arbitrary,
    (\a b -> PrimOp Plus [a,b]) <$> gaen <*> gaen <*> arbitrary,
    (\a b c -> PrimOp IfZ [a,b,c]) <$> gaen <*> gaen <*> gaen <*> arbitrary,
    chooseInt (0,4) >>= (\n -> TupAccess n <$> chooseInt (0,n-1) <*> gaen <*> arbitrary),
    chooseInt (2, min 5 m) >>= (\n -> PrimOp Tup <$> replicateM n gaen <*> arbitrary)
  ]
  where
    gaen  = genArbExpr maxFn n     (m-1)
    gaen1 = genArbExpr maxFn (n+1) (m-1)

typeOrderedCode' :: [Expr a] -> [Type]
typeOrderedCode' = foldl (\ts' h -> ts' <> [fromRight intType $ exprVal <$> annotateExpr ts' (void h)]) []

typeOrderedCode :: [Expr a] -> Code a
typeOrderedCode es = Code $ zip (typeOrderedCode' es) es

shuffleWithMapping :: [a] -> Gen ([(Int, Int)], [a])
shuffleWithMapping l = do
  let r = [0..length l - 1]
  mapping <- shuffle r
  pure (zip mapping r, f mapping l)
  where
    f [] l = []
    f (h:t) l = (l !! h) : f t l

randomizeCodeOrder :: Code a -> Gen (Code a)
randomizeCodeOrder (Code l) = do
  (mapping, l') <- shuffleWithMapping l
  pure $ Code $ (fmap $ second $ replaceFns mapping) l'

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
    c <- typeOrderedCode <$> mapM (\maxFn -> genArbExpr (maxFn-1) 0 size) [0..numFns-1]
    randomizeCodeOrder c
  shrink = genericShrink

printParseTest e = validExpr (-1) e ==> (Right e == parse exprFileParser "" (printExpr e))

betaReducePreservesWellTyped e = validExpr (-1) e ==> isRight (annotateExpr [] e) ==> isRight (annotateExpr [] $ betaReduceFull e)

betaReduceNoLetPreservesWellTyped e = validExpr (-1) e ==> isRight (annotateExpr [] e) ==> isRight (annotateExpr [] $ betaReduce normalBetaReduceSettings { reduceLet = False, reduceIfVals = True } e)

anfIdempotent e = validExpr (-1) e ==> isRight (annotateExpr [] e) ==> (let e' = runAnf e in runAnf e' == e')

anfPreservesType e = validExpr (-1) e ==> isRight te ==> f te tre where
  te = exprVal <$> annotateExpr [] e
  tre = exprVal <$> annotateExpr [] (runAnf e)
  f (Right a) (Right b) = runTypesAlphaEquiv a b
  f _ _ = False

anfPreservesEval e = validExpr (-1) e ==> isRight (annotateExpr [] e) ==> betaReduceFull e == betaReduceFull (runAnf e)

baseEvalInt e = validExpr (-1) e ==> (exprVal <$> annotateExpr [] e) == Right intType ==> f (betaReduceFull e) where
  f (PrimInt _ _) = True
  f _ = False

cpsBaseEvalPreserved e = validExpr (-1) e ==> (exprVal <$> annotateExpr [] e) == Right intType ==> betaReduceNormal e == betaReduceNormal (app (anfWrapCps $ runAnf e) (abs' (evar 0)))

cpsPreservesWellTypedLetless e = validExpr (-1) e ==> isRight (annotateExpr [] e') ==> isRight (annotateExpr [] $ anfWrapCps $ runAnf e') where
  e' = betaReduce (normalBetaReduceSettings { reduceApp = False, reduceIfVals = True }) e

codeTypeCorrect :: Code () -> Property
codeTypeCorrect c = validCode c ==> isRight c' ==> all (uncurry (==)) (second exprVal <$> l') where
  c' = annotateCode c
  Right (Code l') = c'

anfCodePreservesTypes :: Code () -> Property
anfCodePreservesTypes c = validCode c ==> isRight c' ==> (codeTypes <$> c') == (codeTypes <$> a') where
  c' = annotateCode c
  a' = annotateCode $ anfCode c
  codeTypes (Code l) = exprVal . snd <$> l

anfCodePreservesEval :: Code () -> Property
anfCodePreservesEval c = not (null l) ==> validCode c ==> isRight (annotateCode c) ==> head l' == head al' where
  Code l = c
  ac = anfCode c
  f = betaReduceCodeFn fullBetaReduceSettings 0
  Code l' = f c
  Code al' = f ac

anfCodeIdempotent :: Code () -> Property
anfCodeIdempotent c = validCode c ==> isRight (annotateCode c) ==> (let c' = anfCode c in c' == anfCode c')

codeBaseEvalInt :: Code () -> Property
codeBaseEvalInt c = not (null l) ==> validCode c ==> f (annotateCode c) ==> g (betaReduceCodeFn normalBetaReduceSettings 0 c) where
  Code l = c
  f (Right (Code ((t,_):_))) | t == intType = True
  f _ = False
  g (Code l') = h $ snd $ head l'
  h (PrimInt n ()) = True
  h _ = False

regSpillIdempotent :: (Expr (), Int) -> Property
regSpillIdempotent (e,r) = r > 2 ==> r < 5 ==> validExpr (-1) e ==> (let e' = regSpill r $ runAnf e in e' == regSpill r e')

regSpillPreservesType :: (Expr (), Int) -> Property
regSpillPreservesType (e,r) = r > 2 ==> r < 5 ==> validExpr (-1) e ==> isRight (annotateExpr [] e) ==> isRight (annotateExpr [] $ regSpill r $ runAnf e)

regSpillPreservesEval :: (Expr (), Int) -> Property
regSpillPreservesEval (e,r) = r > 2 ==> r < 5 ==> validExpr (-1) e ==> isRight (annotateExpr [] e) ==> betaReduceFull e == betaReduceFull (regSpill r $ runAnf e)

regSpillLimitsMaxReg :: (Expr (), Int) -> Property
regSpillLimitsMaxReg (e,r) = r > 2 ==> r < 5 ==> validExpr (-1) e ==> maxRegAlloced (runRegAlloc $ regSpill r $ runAnf e) <= r

tests :: IO ()
tests = do
  -- tests on Exprs
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =   1000 } printParseTest                    -- haven't written a Code parser/printer yet
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } betaReducePreservesWellTyped      -- not true for Code
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } betaReduceNoLetPreservesWellTyped -- not true for Code
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } cpsBaseEvalPreserved              -- haven't made CPS for Code yet
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } cpsPreservesWellTypedLetless      -- haven't made CPS for Code yet
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 500000 } regSpillIdempotent                -- haven't made regSpill for Code yet (easy tho)
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 500000 } regSpillPreservesEval             -- haven't made regSpill for Code yet (easy tho)
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 500000 } regSpillPreservesType             -- haven't made regSpill for Code yet (easy tho)
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 500000 } regSpillLimitsMaxReg              -- haven't made regSpill for Code yet (easy tho)
  -- tests on Code
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } codeTypeCorrect
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } anfCodePreservesTypes
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } anfCodePreservesEval
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } anfCodeIdempotent
  quickCheckWith stdArgs { maxSize = 9, maxSuccess =  50000 } codeBaseEvalInt

fullTests :: IO ()
fullTests = do
  tests
  -- do things for Expr that have already been done for Code
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfPreservesType
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfPreservesEval
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } baseEvalInt
  quickCheckWith stdArgs { maxSize = 9, maxSuccess = 50000 } anfIdempotent
