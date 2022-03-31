module Compiler.RegAlloc where

import Prelude hiding (abs)
import Data.Tuple.Extra (first, second)
import Data.Maybe (fromJust)
import Compiler.Types

type RegMap = [(Int, Register)]

regAllocAddToMap :: RegMap -> Int -> RegMap
regAllocAddToMap m v
  | v `elem` (fst <$> m) = m
  | otherwise = (v, head $ filter (not . flip elem (snd <$> m)) [0..]) : m

regAllocModifyMap :: RegMap -> Expr () -> RegMap
regAllocModifyMap m e = filter (flip elem fv . fst) $ foldl regAllocAddToMap m fv where fv = freeVars e

-- assumes ANF converted
regAlloc :: RegMap -> Expr () -> Expr RegMap

-- TODO this case should be unused if lambda lifted, ie in the real compilation stack
regAlloc m l@(Let (Abs t x ()) y ()) = Let (Abs t (regAlloc m' x) m') (regAlloc (first (+1) <$> m') y) m' where m' = regAllocModifyMap m l

regAlloc m l@(Abs t x ()) = Abs t (regAlloc m' x) m' where m' = regAllocModifyMap m l
regAlloc m l@(Let x y ()) = Let (m' <$ x) (regAlloc (first (+1) <$> m') y) m' where m' = regAllocModifyMap m l
regAlloc m e = regAllocModifyMap m e <$ e

runRegAlloc :: Expr () -> Expr RegMap
runRegAlloc = regAlloc []

regAllocFn' :: Int -> Expr () -> Expr RegMap
regAllocFn' n (Abs t x ()) = Abs t (regAllocFn' (n+1) x) []
regAllocFn' n a = regAlloc [(i,n-i-1) | i <- [0..n-1]] a

regAllocFn :: Expr () -> Expr RegMap
regAllocFn = regAllocFn' 0

regAllocCode :: Code () -> Code RegMap
regAllocCode (Code l) = Code $ second regAllocFn <$> l

maxRegAlloced :: Expr RegMap -> Register
maxRegAlloced = maximum . fmap (maximum . (-1:) . fmap snd)

lookupRegMapMaybe :: Int -> RegMap -> Maybe Register
lookupRegMapMaybe = lookup

lookupRegMap :: Int -> RegMap -> Register
lookupRegMap n m = fromJust $ lookupRegMapMaybe n m
