module Compiler.HM where

import Prelude hiding (abs)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (StateT, State, get, gets, put, modify, runStateT, runState)
import Data.Tuple.Extra (first, second, both)
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
freeTVars _ = empty

freeTVarsEnv :: [Type] -> Set Int
freeTVarsEnv = fold . fmap freeTVars

replaceTVar :: Int -> Int -> Type -> Type
replaceTVar n m (TVar p) | p == n = TVar m
replaceTVar n m (Fn a b) = Fn (replaceTVar n m a) (replaceTVar n m b)
replaceTVar _ _ a = a

replaceTVars :: [(Int, Int)] -> Type -> Type
replaceTVars = foldr (.) id . fmap (uncurry replaceTVar)

-- note: every var only ever shows up as a GVTVar or a TVar, never both
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

repeatedInstantiateSt :: [(Type, Type)] -> Type -> State ([(Int, Int)], Int) Type
repeatedInstantiateSt constrs t = do
  lengthBefore <- gets $ length . fst
  t' <- instantiateSt t
  mapAfter <- gets fst
  let ldiff = length mapAfter - lengthBefore
  if ldiff == 0
    then pure ()
    else do
      -- TODO call repeatedInstantiateSt on all related variables in constrs
      pure ()
  pure t'

instantiate :: Type -> State ([(Type, Type)], Int) Type
instantiate t = do
  (constrs, n) <- get
  let (tt, (gtmap, nn)) = runState (repeatedInstantiateSt constrs t) ([], n)
  modify (second $ const nn)
  sequence $ f gtmap <$> constrs
  pure tt
  where
    f gtmap (ta, tb) | ta' /= ta || tb' /= tb = addConstr (ta', tb') where
      ta' = replaceTVars gtmap ta
      tb' = replaceTVars gtmap tb
    f _ _ = pure ()

-- do not use for anything except for prim vals; breaks on weird edge cases
typeToCPS :: Type -> State (a, Int) Type
typeToCPS (Fn a b) = do
  a' <- typeToCPS a
  b' <- typeToCPS b
  v  <- newTypeVar
  pure $ Fn a' (Fn (Fn b' v) v)
typeToCPS t = pure t

-- note: GTVars never get added to the constraint set
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
gather env (PrimOp Plus [a,b] ()) = do
  ga <- gather env a
  gb <- gather env b
  let (ta, tb) = both exprVal (ga, gb)
  addConstr (ta, intType)
  addConstr (tb, intType)
  pure $ PrimOp Plus [ga, gb] intType

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
