{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module Compiler.Types where

import Prelude hiding (abs)
import GHC.Generics (Generic)
import Control.Monad (mzero, replicateM)
import Data.Maybe (maybe, isJust)
import Control.Monad.State (StateT, runStateT, gets, modify)

data PrimOpEnum = Plus | Tup | IfZ   deriving (Show, Eq, Generic)
data PrimTypeEnum = IntT   deriving (Show, Eq, Generic)
data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Maybe Type) (Expr a) a | Let (Expr a) (Expr a) a | PrimInt Integer a | TupAccess Int Int (Expr a) a | PrimOp PrimOpEnum [Expr a] a | FnVal Int a  deriving (Show, Eq, Functor, Generic)
data Type = PrimT PrimTypeEnum | TupT [Type] | Fn Type Type | TVar Int   deriving (Show, Eq, Generic)
newtype Code a = Code [(Type, Expr a)] deriving (Eq, Show, Generic)

evar n = EVar n ()
app a b = App a b ()
abs t a = Abs t a ()
abs' = abs Nothing
let' a b = Let a b ()
primInt n = PrimInt n ()
tupAccess n m a = TupAccess n m a ()
primOp s e = PrimOp s e ()
fnVal n = FnVal n ()

exprVal :: Expr a -> a
exprVal (EVar          _ q) = q
exprVal (App         _ _ q) = q
exprVal (Abs         _ _ q) = q
exprVal (Let         _ _ q) = q
exprVal (PrimInt       _ q) = q
exprVal (TupAccess _ _ _ q) = q
exprVal (PrimOp      _ _ q) = q
exprVal (FnVal         _ q) = q

validAbsType :: Type -> Bool
validAbsType (PrimT _) = True
validAbsType (TupT l) = all validAbsType l
validAbsType (Fn a b) = validAbsType a && validAbsType b
validAbsType _ = False -- TODO what abt type variables?

goodNumArgs :: PrimOpEnum -> Int -> Bool
goodNumArgs Plus n = n == 2
goodNumArgs Tup  n = n > 1
goodNumArgs IfZ  n = n == 3

validExpr' :: Int -> Int -> Expr () -> Bool
validExpr' maxFn n (EVar m ()) = m < n && m >= 0
validExpr' maxFn n (App a b ()) = validExpr' maxFn n a && validExpr' maxFn n b
validExpr' maxFn n (Abs t a ()) = maybe True validAbsType t && validExpr' maxFn (n+1) a
validExpr' maxFn n (Let a b ()) = validExpr' maxFn n a && validExpr' maxFn (n+1) b
validExpr' maxFn n (PrimInt _ ()) = True
validExpr' maxFn n (TupAccess nn m a ()) = nn >= 0 && m >= 0 && m > nn && validExpr' maxFn n a
validExpr' maxFn n (PrimOp o l ()) = goodNumArgs o (length l) && all (validExpr' maxFn n) l
validExpr' maxFn n (FnVal m ()) = m >= 0 && m < n && m <= maxFn -- TODO why does this even get called inth e first place

validExpr :: Int -> Expr () -> Bool
validExpr maxFn = validExpr' maxFn 0

incVars :: Int -> Expr a -> Expr a
incVars n (EVar m q) | m >= n = EVar (m+1) q
incVars n (App x y q) = App (incVars n x) (incVars n y) q
incVars n (Abs t x q) = Abs t (incVars (n+1) x) q
incVars n (Let x y q) = Let (incVars n x) (incVars (n+1) y) q
incVars n (TupAccess nn m a q) = TupAccess nn m (incVars n a) q
incVars n (PrimOp a l q) = PrimOp a (incVars n <$> l) q
incVars n x = x

replaceVar :: Int -> Expr a -> Expr a -> Expr a
replaceVar m a (EVar n _) | m == n = a
replaceVar m a (EVar n q) | m < n = EVar (n-1) q
replaceVar m a (App x y q) = App (replaceVar m a x) (replaceVar m a y) q
replaceVar m a (Abs t x q) = Abs t (replaceVar (m+1) (incVars 0 a) x) q
replaceVar m a (Let x y q) = Let (replaceVar m a x) (replaceVar (m+1) (incVars 0 a) y) q
replaceVar m a (TupAccess n mm x q) = TupAccess n mm (replaceVar m a x) q
replaceVar m a (PrimOp o l q) = PrimOp o (replaceVar m a <$> l) q
replaceVar _ _ x = x

replaceType :: Int -> Type -> Type -> Type
replaceType n t (TVar m) | m == n = t
replaceType n t (Fn a b) = Fn (replaceType n t a) (replaceType n t b)
replaceType n t (TupT l) = TupT $ replaceType n t <$> l
replaceType _ _ a = a

-- TODO nooo you can't just be inefficient
replaceTypes :: [(Int, Type)] -> Type -> Type
replaceTypes = foldr (.) id . fmap (uncurry replaceType)

hasTV :: Int -> Type -> Bool
hasTV n (TVar m) = n == m
hasTV n (Fn a b) = hasTV n a || hasTV n b
hasTV n (TupT l) = any (hasTV n) l
hasTV _ _ = False

maxTypeVar :: Type -> Int
maxTypeVar (TVar n) = n
maxTypeVar (Fn a b) = max (maxTypeVar a) (maxTypeVar b)
maxTypeVar (TupT l) = maximum $ maxTypeVar <$> l
maxTypeVar _ = -1

intType :: Type
intType = PrimT IntT

typesAlphaEquiv :: Type -> Type -> StateT [(Int, Int)] Maybe ()
typesAlphaEquiv (TVar n) (TVar m) = do
  s <- gets $ lookup n
  maybe tryAddVar checkVar s
  where
    tryAddVar = do
      s <- gets $ lookup m . fmap (\(a,b) -> (b,a))
      maybe addVar (const mzero) s
    addVar = modify ((n,m):)
    checkVar b = if b == m then pure () else mzero
typesAlphaEquiv (Fn a b) (Fn c d) = typesAlphaEquiv a c >> typesAlphaEquiv b d
typesAlphaEquiv (PrimT a) (PrimT b) = if a == b then pure () else mzero
typesAlphaEquiv (TupT a) (TupT b) = if length a /= length b then mzero else sequence_ (uncurry typesAlphaEquiv <$> zip a b)
typesAlphaEquiv _ _ = mzero

runTypesAlphaEquiv :: Type -> Type -> Bool
runTypesAlphaEquiv a b = isJust $ runStateT (typesAlphaEquiv a b) []
