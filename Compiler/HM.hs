module Compiler.HM where

import Prelude hiding (abs)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (StateT, State, get, gets, put, modify, runStateT, runState)
import Data.Tuple.Extra (first, second, both, dupe, (***))
import Data.Set (Set, empty, singleton, member)
import Data.Maybe (maybe)
import Data.Foldable (fold)
import Compiler.Types

newTypeVarNum :: State (a, Int) Int
newTypeVarNum = modify (second (+ 1)) >> gets snd

newTypeVar :: State (a, Int) Type
newTypeVar = TVar <$> newTypeVarNum

addConstr :: a -> State ([a], b) ()
addConstr h = modify $ first (h:)

freeTVars :: Type -> Set Int
freeTVars (Fn a b) = freeTVars a <> freeTVars b
freeTVars (TVar n) = singleton n
freeTVars (TupT l) = fold $ freeTVars <$> l
freeTVars _ = empty

freeTVarsEnv :: [Type] -> Set Int
freeTVarsEnv = fold . fmap freeTVars

replaceTVar :: Int -> Int -> Type -> Type
replaceTVar n m (TVar p) | p == n = TVar m
replaceTVar n m (Fn a b) = Fn (replaceTVar n m a) (replaceTVar n m b)
replaceTVar n m (TupT l) = TupT $ replaceTVar n m <$> l
replaceTVar _ _ a = a

replaceTVars :: [(Int, Int)] -> Type -> Type
replaceTVars = foldr (.) id . fmap (uncurry replaceTVar)

instantiateMapVars :: Int -> (Int, Int) -> (Int, [(Int, Int)])
instantiateMapVars n (a,b) = (n+b-a+1, f <$> [0..b-a]) where
  f m = (a+m, n+1+m)

instantiate :: (Int,Int) -> Type -> State ([(Type, Type)], Int) Type
instantiate r t = do
  n <- gets snd
  let (n', gtmap) = instantiateMapVars n r
  modify (second $ const n')
  constrs <- gets fst
  sequence $ fmap (addConstr . snd) $ filter (uncurry (/=)) $ fmap ((id *** both (replaceTVars gtmap)) . dupe) constrs
  pure $ replaceTVars gtmap t

-- note: GTVars never get added to the constraint set
gather :: [((Int,Int),Type)] -> Expr () -> State ([(Type, Type)], Int) (Expr Type)
gather env (EVar n ()) = uncurry instantiate (env !! n) >>= pure . (EVar n)
gather env (App a b ()) = do
  ga <- gather env a
  gb <- gather env b
  v  <- newTypeVar
  let (ta, tb) = (exprVal ga, exprVal gb)
  addConstr (ta, Fn tb v)
  pure $ App ga gb v
gather env (Abs tv a ()) = do
  v <- maybe newTypeVar pure tv
  g <- gather (((1,0),v):env) a
  let t = exprVal g
  pure $ Abs tv g $ Fn v t
gather env (Let a b ()) = do
  n <- gets snd
  ga <- gather env a
  n' <- gets snd
  gb <- gather (((n+1,n'),exprVal ga):env) b
  pure $ Let ga gb $ exprVal gb
gather env (PrimInt n ()) = pure $ PrimInt n intType
gather env (PrimOp o l ()) = do
  gl <- sequence $ gather env <$> l
  PrimOp o gl <$> primOpType o (exprVal <$> gl)

primOpType :: PrimOpEnum -> [Type] -> State ([(Type, Type)], Int) Type
primOpType Plus [ta,tb] = do
  addConstr (ta, intType)
  addConstr (tb, intType)
  pure intType
primOpType Tup tl = pure $ TupT tl
primOpType IfZ [ta, tb, tc] = do
  addConstr (ta, intType)
  addConstr (tb, tc)
  pure tb

runGather :: Expr () -> (Expr Type, [(Type, Type)])
runGather = second fst . flip runState ([], 0) . gather []

addUnify :: (Monad m) => (Int, Type) -> StateT [(Int, Type)] m ()
addUnify a = modify (a:)

replaceUnify :: Int -> Type -> [(Type, Type)] -> [(Type, Type)]
replaceUnify n t = fmap (both $ replaceType n t)

unify :: [(Type, Type)] -> StateT [(Int, Type)] (Either String) ()
unify [] = pure ()
unify ((a,b):r) | a == b = unify r
unify ((Fn a b, Fn c d):r) = unify ((a,c):(b,d):r)
unify ((TupT a, TupT b):r) = if length a /= length b
                               then lift $ Left $ "Cannot unify two tuples of different size: TupT " <> show a <> " and TupT " <> show b
                               else unify (zip a b <> r)
unify ((TVar n, a):r)
  | hasTV n a = lift $ Left $ "Cannot construct infinte type " <> show (TVar n) <> " = " <> show a
  | otherwise = addUnify (n, a) >> unify (replaceUnify n a r)
unify ((a, TVar n):r) = unify ((TVar n, a):r)
unify (c:_) = lift $ Left $ "Failed to unify constraint " <> show c

runUnify :: [(Type, Type)] -> Either String [(Int, Type)]
runUnify t = snd <$> runStateT (unify t) []

annotateExpr :: Expr () -> Either String (Expr Type)
annotateExpr e = do
  let (ge, tt) = runGather e
  solved <- runUnify tt
  pure $ replaceTypes solved <$> ge
