{-# LANGUAGE DeriveFunctor #-}

import Prelude hiding (abs)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (State, get, gets, put, modify, runState)
import Control.Monad.Trans.Either (EitherT, runEitherT, left)
import Data.Tuple.Extra (first, second, both)
import Data.Set (Set, empty, singleton, member)
import Data.Maybe (maybe)
import Data.Foldable (fold)

-- type argument on Abs may not have any GTVars
data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Maybe Type) (Expr a) a | Let (Expr a) (Expr a) a | PrimInt Integer a | PrimVal String a  deriving (Show, Eq, Functor)
data Type = PrimT String | Fn Type Type | TVar Int | GTVar Int   deriving (Show, Eq)

evar n = EVar n ()
app a b = App a b ()
abs t a = Abs t a ()
abs' = abs Nothing
let' a b = Let a b ()
primInt n = PrimInt n ()
primVal s = PrimVal s ()

exprVal :: Expr a -> a
exprVal (EVar    _ q) = q
exprVal (App   _ _ q) = q
exprVal (Abs   _ _ q) = q
exprVal (Let   _ _ q) = q
exprVal (PrimInt _ q) = q
exprVal (PrimVal _ q) = q

incVars :: Int -> Expr a -> Expr a
incVars n (EVar m q) | m >= n = EVar (m+1) q
incVars n (App x y q) = App (incVars n x) (incVars n y) q
incVars n (Abs t x q) = Abs t (incVars (n+1) x) q
incVars n (Let x y q) = Let (incVars n x) (incVars (n+1) y) q
incVars n x = x

replaceVar :: Int -> Expr a -> Expr a -> Expr a
replaceVar m a (EVar n _) | m == n = a
replaceVar m a (App x y q) = App (replaceVar m a x) (replaceVar m a y) q
replaceVar m a (Abs t x q) = Abs t (replaceVar (m+1) (incVars 0 a) x) q
replaceVar m a (Let x y q) = Let (replaceVar m a x) (replaceVar (m+1) (incVars 0 a) y) q
replaceVar _ _ x = x

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
gather env (PrimVal "+" ()) = pure $ PrimVal "+" $ Fn intType intType -- Fn intType (Fn intType intType)

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
  let a = abs' $ abs' $ app (app (primVal "+") (evar 1)) (evar 1)
  let b = let' (abs' $ evar 0) $ app (app (evar 0) (evar 0)) (primInt 0)
  let c = app (primVal "+") (primInt 0)
  let p = putStrLn
  let f = p . show . annotateExpr
  let g = p . show . fmap exprVal . annotateExpr
  let r = runAnf
  g $ a
  g $ b
  f $ b
  g $ abs (Just intType) (evar 0)
  f $ abs (Just intType) $ app (evar 0) (primInt 0)
  g $ abs' $ app (evar 0) (primInt 0)
  p $ "sneed"
  g $ c
  p $ show $ r c
  f $ r c
  g $ r c
  g $ r $ r c

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
anf a l c = c a l

runAnf :: Expr () -> Expr ()
runAnf a = anf a [] (\a' [] -> a')
