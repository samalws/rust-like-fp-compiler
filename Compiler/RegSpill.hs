module Compiler.RegSpill where

import Prelude hiding (abs)
import Data.Set (toList, size)
import Compiler.Types

doRegSpill :: Int -> Expr () -> Expr ()
doRegSpill r e = let' tup $ regSpill r $ replaceVars mapping e where
  fv = toList $ freeVars e
  tup = primOp Tup $ evar <$> fv
  mapping = fv `zip` fmap (\n -> tupAccess n (length fv) (evar 0)) [0..]

-- max register -> expr -> expr
-- assumption: code has been CPS'd
-- TODO feel like I'm making an off by one error here
-- TODO also it's not idempotent why?!??!?!
regSpill :: Register -> Expr () -> Expr ()
regSpill r l@(Let _ _ ()) | size (freeVars l) >= r = doRegSpill r l
regSpill r l@(Let (Abs t x ()) y ()) = let' (abs t $ regSpill r x) $ regSpill r y
regSpill r l@(Let x y ()) = let' x $ regSpill r y
regSpill r x = x
