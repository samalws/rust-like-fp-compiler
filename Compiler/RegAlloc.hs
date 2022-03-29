module Compiler.RegAlloc where

import Prelude hiding (abs)
import Data.Tuple.Extra (first)
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
regAlloc m l@(Let (Abs t x ()) y ()) = Let (Abs t (regAlloc m' x) m') (regAlloc (first (+1) <$> m') y) m' where m' = regAllocModifyMap m l
regAlloc m l@(Let x            y ()) = Let (m' <$ x)                  (regAlloc (first (+1) <$> m') y) m' where m' = regAllocModifyMap m l
regAlloc m e = regAllocModifyMap m e <$ e

runRegAlloc :: Expr () -> Expr RegMap
runRegAlloc = regAlloc []

maxRegAlloced :: Expr RegMap -> Register
maxRegAlloced = maximum . fmap (maximum . (-1:) . fmap snd)

lookupRegMap :: Int -> RegMap -> Register
lookupRegMap n m = fromJust $ lookup n m
