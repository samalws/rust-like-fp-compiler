module Compiler.CPS where

import Prelude hiding (abs)
import Compiler.Types

anfToCps :: Expr () -> Expr () -> Expr ()
anfToCps r (Let (App a b ()) c ()) = let' (abs' $ anfToCps (incVars 0 r) c) (app (app (incVars 0 a) (incVars 0 b)) (evar 0))
anfToCps r (Let (Abs _ a ()) c ()) = let' (abs' $ abs' $ anfToCps (evar 0) $ incVars 0 a) (anfToCps (incVars 0 r) c)
anfToCps r (Let a c ()) = let' a $ anfToCps (incVars 0 r) c
anfToCps r a = app r a

anfWrapCps :: Expr () -> Expr ()
anfWrapCps = abs' . anfToCps (evar 0)
