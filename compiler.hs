{-# LANGUAGE DeriveFunctor #-}

import Prelude hiding (abs)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (State, get, gets, put, modify, runState)
import Control.Monad.Trans.Either (EitherT, runEitherT, left)
import Data.Tuple.Extra (first, second, both)
import Data.Set (Set, empty, singleton, member)
import Data.Maybe (maybe)
import Data.Foldable (fold)

data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Maybe Type) (Expr a) a | Let (Expr a) (Expr a) a | PrimInt Integer a | PrimVal String a  deriving (Show, Eq, Functor)
data Type = PrimT String | Fn Type Type | TVar Int | GTVar Int   deriving (Show, Eq)

evar n = EVar n ()
app a b = App a b ()
abs' t a = Abs (Just t) a ()
abs a = Abs Nothing a ()
let' a b = Let a b ()
primInt n = PrimInt n ()
primVal s = PrimVal s ()

exprVal :: Expr a -> a
exprVal (EVar    _ a) = a
exprVal (App   _ _ a) = a
exprVal (Abs   _ _ a) = a
exprVal (Let   _ _ a) = a
exprVal (PrimInt _ a) = a
exprVal (PrimVal _ a) = a

incFreeVars :: Int -> Expr a -> Expr a
incFreeVars n (EVar m a) | m >= n = EVar (m+1) a
incFreeVars n (App x y a) = App (incFreeVars n x) (incFreeVars n y) a
incFreeVars n (Abs t x a) = Abs t (incFreeVars (n+1) x) a
incFreeVars n (Let x y a) = Let (incFreeVars n x) (incFreeVars (n+1) y) a
incFreeVars n x = x

replaceType :: Int -> Type -> Type -> Type
replaceType n t (TVar m) | m == n = t
replaceType n t (Fn a b) = Fn (replaceType n t a) (replaceType n t b)
replaceType _ _ a = a

-- TODO nooo you can't just be inefficient
replaceTypes :: [(Int, Type)] -> Type -> Type
replaceTypes = foldr (.) id . fmap (uncurry replaceType)

hasTV :: Int -> Type -> Bool
hasTV n (TVar m) = n == m
hasTV n (Fn a b) = hasTV n a || hasTV n b
hasTV _ _ = False

intType :: Type
intType = PrimT "int"

newTypeVarNum :: State (a, Int) Int
newTypeVarNum = modify (second (+ 1)) >> gets snd

newTypeVar :: State (a, Int) Type
newTypeVar = TVar <$> newTypeVarNum

addConstr :: a -> State ([a], b) ()
addConstr h = modify $ first (h:)

freeTVars :: Type -> Set Int
freeTVars (Fn a b) = freeTVars a <> freeTVars b
freeTVars (TVar n) = singleton n
freeTVars _ = empty

freeTVarsEnv :: [Type] -> Set Int
freeTVarsEnv = fold . fmap freeTVars

generalize :: Set Int -> Type -> Type
generalize s (TVar n) | not (member n s) = GTVar n
generalize s (Fn a b) = Fn (generalize s a) (generalize s b)
generalize _ a = a

instantiateSt :: Type -> State ([(Int, Int)], Int) Type
instantiateSt (GTVar n) = gets fst >>= maybe f (pure . TVar) . lookup n where
  f = do
    v <- newTypeVarNum
    modify $ first ((n, v):)
    pure $ TVar v
instantiateSt (Fn a b) = Fn <$> instantiateSt a <*> instantiateSt b
instantiateSt a = pure a

instantiate :: Type -> State (a, Int) Type
instantiate t = do
  n <- gets snd
  let (tt, (_, nn)) = runState (instantiateSt t) ([], n)
  modify (second $ const nn)
  pure tt

gather :: [Type] -> Expr () -> State ([(Type, Type)], Int) (Expr Type)
gather env (EVar n ()) = instantiate (env !! n) >>= pure . (EVar n)
gather env (App a b ()) = do
  ga <- gather env a
  gb <- gather env b
  v  <- newTypeVar
  let (ta, tb) = (exprVal ga, exprVal gb)
  addConstr (ta, Fn tb v)
  pure $ App ga gb v
gather env (Abs tv a ()) = do
  v <- maybe newTypeVar pure tv
  g <- gather (v:env) a
  let t = exprVal g
  pure $ Abs tv g $ Fn v t
gather env (Let a b ()) = do
  ga0 <- gather env a
  let ga = generalize (freeTVarsEnv env) <$> ga0
  gb <- gather ((exprVal ga):env) b
  pure $ Let ga gb $ exprVal gb
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
runUnify = uncurry f . flip runState [] . runEitherT . unify   where f a s = a >> pure s

annotateExpr :: Expr () -> Either String (Expr Type)
annotateExpr e = do
  let (ge, tt) = runGather e
  solved <- runUnify tt
  pure $ replaceTypes solved <$> ge

main = do
  print $ fmap exprVal $ annotateExpr $ abs $ abs $ app (app (primVal "+") (evar 1)) (evar 1)
  print $ fmap exprVal $ annotateExpr $ let' (abs $ evar 0) $ app (app (evar 0) (evar 0)) (primInt 0)
  print $ annotateExpr $ let' (abs $ evar 0) $ app (app (evar 0) (evar 0)) (primInt 0)
  print $ fmap exprVal $ annotateExpr $ abs' intType (evar 0)
  print $ annotateExpr $ abs' intType $ app (evar 0) (primInt 0)
  print $ fmap exprVal $ annotateExpr $ abs $ app (evar 0) (primInt 0)
