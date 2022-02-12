module Compiler.AddBlankAbses where

import Prelude hiding (abs)
import Data.Tuple.Extra (second)
import Compiler.Types

-- TODO change it from intType to voidType when I make that

addBlankAbses' :: Code () -> ([Int], Code ())
addBlankAbses' (Code []) = ([], Code [])
addBlankAbses' (Code (h@(_, Abs {}):r)) = ((+1) <$> l, Code (h:r'))                               where (l,Code r') = addBlankAbses' (Code r)
addBlankAbses' (Code ((t,h):r)) = (0:((+1) <$> l), Code ((TVar v `Fn` t, Abs Nothing h ()) : r')) where (l,Code r') = addBlankAbses' (Code r)
                                                                                                        v = maxTypeVar t + 1

replaceBlankAbses :: [Int] -> Expr () -> Expr ()
replaceBlankAbses ns (FnVal m ()) | m `elem` ns = app (fnVal m) (primInt 0)
replaceBlankAbses ns (App a b ()) = app (replaceBlankAbses ns a) (replaceBlankAbses ns b)
replaceBlankAbses ns (Abs t a ()) = abs t (replaceBlankAbses ns a)
replaceBlankAbses ns (Let a b ()) = let' (replaceBlankAbses ns a) (replaceBlankAbses ns b)
replaceBlankAbses ns (TupAccess n m a ()) = tupAccess n m (replaceBlankAbses ns a)
replaceBlankAbses ns (PrimOp o l ()) = primOp o (replaceBlankAbses ns <$> l)
replaceBlankAbses ns a = a

replaceBlankAbsesCode :: [Int] -> Code () -> Code ()
replaceBlankAbsesCode ns (Code l) = Code (second (replaceBlankAbses ns) <$> l)

addBlankAbses :: Code () -> Code ()
addBlankAbses = uncurry replaceBlankAbsesCode . addBlankAbses'
