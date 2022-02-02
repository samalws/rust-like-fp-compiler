{-# LANGUAGE DeriveFunctor #-}

import Prelude hiding (abs)
import Control.Monad.State
import Control.Monad.Trans.Either
import Data.Tuple.Extra (first, second, both)

data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Expr a) a | PrimInt Integer a | PrimVal String a   deriving (Show, Eq, Functor)  -- | Let Expr Expr
data Type = PrimT String | Fn Type Type | TVar Int   deriving (Show, Eq)
-- data PolyType = Concrete Type | Forall PolyType

evar n = EVar n ()
app a b = App a b ()
abs a = Abs a ()
primInt n = PrimInt n ()
primVal s = PrimVal s ()

exprVal :: Expr a -> a
exprVal (EVar    _ a) = a
exprVal (App   _ _ a) = a
exprVal (Abs     _ a) = a
exprVal (PrimInt _ a) = a
exprVal (PrimVal _ a) = a

replaceType :: Int -> Type -> Type -> Type
replaceType n t (TVar m) | m == n = t
replaceType n t (Fn a b) = Fn (replaceType n t a) (replaceType n t b)
replaceType _ _ a = a

replaceTypes :: [(Int, Type)] -> Type -> Type
replaceTypes = foldr (.) id . fmap (uncurry replaceType)

hasTV :: Int -> Type -> Bool
hasTV n (TVar m) = n == m
hasTV n (Fn a b) = hasTV n a || hasTV n b
hasTV _ _ = False

intType :: Type
intType = PrimT "int"

newTypeVar :: State (a, Int) Type
newTypeVar = modify (second (+ 1)) >> gets (TVar . snd)

addConstr :: a -> State ([a], b) ()
addConstr h = modify $ first (h:)

gather :: [Type] -> Expr () -> State ([(Type, Type)], Int) (Expr Type)
gather env (EVar n ()) = pure $ EVar n $ env !! n
gather env (App a b ()) = do
  ga <- gather env a
  gb <- gather env b
  v  <- newTypeVar
  let (ta, tb) = (exprVal ga, exprVal gb)
  addConstr (ta, Fn tb v)
  pure $ App ga gb v
gather env (Abs a ()) = do
  v <- newTypeVar
  g <- gather (v:env) a
  let t = exprVal g
  pure $ Abs g $ Fn v t
gather env (PrimInt n ()) = pure $ PrimInt n intType
gather env (PrimVal "+" ()) = pure $ PrimVal "+" $ Fn intType (Fn intType intType)

runGather :: Expr () -> (Expr Type, [(Type, Type)])
runGather = second fst . flip runState ([], 0) . gather []

addUnify :: (Int, Type) -> State [(Int, Type)] ()
addUnify a = modify (a:)

replaceUnify :: Int -> Type -> [(Type, Type)] -> [(Type, Type)]
replaceUnify n t = fmap (both $ replaceType n t)

unify :: [(Type, Type)] -> EitherT String (State [(Int, Type)]) ()
unify [] = pure ()
unify ((a,b):r) | a == b = unify r
unify ((Fn a b, Fn c d):r) = unify ((a,c):(b,d):r)
unify ((TVar n, a):r)
  | hasTV n a = left $ "Cannot construct infinte type " <> show (TVar n) <> " = " <> show a
  | otherwise = lift (addUnify (n, a)) >> unify (replaceUnify n a r)
unify ((a, TVar n):r) = unify ((TVar n, a):r)
unify (c:_) = left $ "Failed to unify constraint " <> show c

runUnify :: [(Type, Type)] -> Either String [(Int, Type)]
runUnify = fmap reverse . uncurry f . flip runState [] . runEitherT . unify   where f a s = a >> pure s

annotateExpr :: Expr () -> Either String (Expr Type)
annotateExpr e = do
  let (ge, tt) = runGather e
  solved <- runUnify tt
  pure $ replaceTypes solved <$> ge

main = print $ annotateExpr $ abs $ abs $ app (app (primVal "+") (evar 1)) (evar 1)
