module Compiler.CPS where

import Prelude hiding (abs)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.Function.HT (nest)
import Compiler.Types

-- might produce "ill-typed" terms, if there are self-calls involved
-- "ill-typed" due to Abs arguments not being polymorphic
-- super janky example: let f = (\x. \y. 5) 6 in f f   anf preserves type, but cps breaks the type (but will still work)
-- this is okay though, it gets fixed during closure conversion

anfToCpsFull :: (Monad m) => (Int -> Expr () -> m (Expr ())) -> (Expr () -> Expr () -> Expr ()) -> Expr () -> Expr () -> m (Expr ())
anfToCpsFull g h r (Let (App a b ()) c ()) = let' <$> (g 1 =<< anfToCpsFull g h (incVars 0 r) c) <*> pure ((incVars 0 a `app` incVars 0 b) `app` evar 0)
anfToCpsFull g h r (Let (Abs _ a ()) c ()) = let' <$> (g 2 =<< anfToCpsFull g h (evar 0) (incVars 0 a)) <*> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (Let a c ()) = let' a <$> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (App a b ()) = pure $ (a `app` b) `app` r
anfToCpsFull g h r a = pure $ h r a

anfToCps :: Expr () -> Expr () -> Expr ()
anfToCps = (runIdentity .) . anfToCpsFull ((Identity .) . flip nest abs') app

anfWrapCps :: Expr () -> Expr ()
anfWrapCps = abs' . anfToCps (evar 0)
