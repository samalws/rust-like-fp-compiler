module Compiler.CPS where

import Prelude hiding (abs)
import Compiler.Types

-- might produce "ill-typed" terms, if there are self-calls involved
-- "ill-typed" due to Abs arguments not being polymorphic
-- super janky example: let f = (\x. \y. 5) 6 in f f   anf preserves type, but cps breaks the type (but will still work)
-- possible fix later might be to plug in let values with differing types *before* doing cps conversion
-- TODO

anfToCps :: Expr () -> Expr () -> Expr ()
anfToCps r (Let (App a b ()) c ()) = let' (abs' $ anfToCps (incVars 0 r) c) (app (app (incVars 0 a) (incVars 0 b)) (evar 0))
anfToCps r (Let (Abs _ a ()) c ()) = let' (abs' $ abs' $ anfToCps (evar 0) $ incVars 0 a) (anfToCps (incVars 0 r) c)
anfToCps r (Let a c ()) = let' a $ anfToCps (incVars 0 r) c
anfToCps r a = app r a

anfWrapCps :: Expr () -> Expr ()
anfWrapCps = abs' . anfToCps (evar 0)
