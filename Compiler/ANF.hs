module Compiler.ANF where

import Prelude hiding (abs)
import Compiler.Types

anf :: Expr () -> [Expr ()] -> (Expr () -> [Expr ()] -> Expr ()) -> Expr ()
anf (App a b ())    l r = anfTransportVals [a,b] l (\[a',b'] l' -> let' (app a' b')   (r (evar 0) (map (incVars 0) l')))
anf (PrimOp o x ()) l r = anfTransportVals x     l (\x'      l' -> let' (primOp o x') (r (evar 0) (map (incVars 0) l')))
anf (Abs t a ()) l r = let'
                         (abs t (runAnf a))
                         (r (evar 0) (map (incVars 0) l))
anf (Let a b ()) l r = anf a (evar 0:b:l) (\a' ((EVar z' ()):b':l') ->
                       anf (replaceVar z' a' b') l' r)
anf (TupAccess n m a ()) l r = anf a l (r . tupAccess n m) -- thanks quickcheck
anf a l r = r a l

anfTransportVals' :: Int -> [Expr ()] -> [Expr ()] -> ([Expr ()] -> [Expr ()] -> Expr ()) -> Expr ()
anfTransportVals' 0 x l r = r x l
anfTransportVals' n [] l r = r [] l
anfTransportVals' n (h:t) l r = anf h (t <> l) (\h' tl' ->
                                let
                                  lent = length t
                                  t' = take lent tl'
                                  l' = drop lent tl'
                                in
                                  anfTransportVals' (n-1) (t' <> [h']) l' r )

anfTransportVals :: [Expr ()] -> [Expr ()] -> ([Expr ()] -> [Expr ()] -> Expr ()) -> Expr ()
anfTransportVals x = anfTransportVals' (length x) x

-- should be idempotent
runAnf :: Expr () -> Expr ()
runAnf a = anf a [] (\a' [] -> a')
