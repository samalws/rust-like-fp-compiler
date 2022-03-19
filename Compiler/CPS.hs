module Compiler.CPS where

import Prelude hiding (abs)
import Compiler.Types

-- might produce "ill-typed" terms, if there are self-calls involved
-- "ill-typed" due to Abs arguments not being polymorphic
-- super janky example: let f = (\x. \y. 5) 6 in f f   anf preserves type, but cps breaks the type (but will still work)
-- possible fix later might be to plug in let values with differing types *before* doing cps conversion
-- TODO

anfToCpsFull :: (Monad m) => (Int -> Expr () -> m (Expr ())) -> (Expr () -> Expr () -> Expr ()) -> Expr () -> Expr () -> m (Expr ())
anfToCpsFull g h r (Let (App a b ()) c ()) = let' <$> (g 1 =<< anfToCpsFull g h (incVars 0 r) c) <*> pure ((incVars 0 a `app` incVars 0 b) `app` evar 0)
anfToCpsFull g h r (Let (Abs _ a ()) c ()) = let' <$> (g 2 =<< anfToCpsFull g h (evar 0) (incVars 0 a)) <*> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (Let a c ()) = let' a <$> anfToCpsFull g h (incVars 0 r) c
anfToCpsFull g h r (App a b ()) = pure $ (a `app` b) `app` r
anfToCpsFull g h r a = pure $ h r a

anfToCps :: Expr () -> Expr () -> Expr ()
anfToCps = (runIdentity .) . anfToCpsFull ((Identity .) . flip nest abs') app

-- TODO this was fine to change right? where do I ever use this?
anfWrapCps :: Expr () -> Expr ()
anfWrapCps = abs' . descendAbses (anfToCps . evar)

cpsConvertCode :: Code () -> Code ()
cpsConvertCode (Code c) = Code $ ??? $ f <$> c where
  f (Abs ta (Abs te x ()) ()) = abs' . abs ta . abs te <$> anfToCpsFull g h (evar 2) x
  g 1 e = TODO
  h r a = ((tupAccess 0 2 e `app` primInt 0) `app` tupAccess 1 2 e) `app` ee -- primInt because we never expect to return from r (TODO jank?)
