module Compiler.ANF where

import Prelude hiding (abs)
import Compiler.Types

anf :: Expr () -> [Expr ()] -> (Expr () -> [Expr ()] -> Expr ()) -> Expr ()
anf (App a b ()) l c = anf a  (b :l ) (\a'  (b' :l' ) ->
                       anf b' (a':l') (\b'' (a'':l'') ->
                         let'
                           (app a'' b'')
                           (c (evar 0) (map (incVars 0) l''))
                       ))
anf (Abs t a ()) l c = let'
                         (abs t (runAnf a))
                         (c (evar 0) (map (incVars 0) l))
anf (Let a b ()) l c = anf a ((evar 0):b:l) (\a' ((EVar z' ()):b':l') ->
                       anf (replaceVar z' a' b') l' (\b'' l'' ->
                       c b'' l'' ))
-- TODO general case?
anf (PrimOp o [a, b] ()) l c = anf a  (b :l ) (\a'  (b' :l' ) ->
                               anf b' (a':l') (\b'' (a'':l'') ->
                                 let'
                                   (primOp o [a'', b''])
                                   (c (evar 0) (map (incVars 0) l''))
                               ))
anf a l c = c a l

-- should be idempotent
runAnf :: Expr () -> Expr ()
runAnf a = anf a [] (\a' [] -> a')
