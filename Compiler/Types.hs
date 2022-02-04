{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module Compiler.Types where

import Prelude hiding (abs)
import Test.QuickCheck.Arbitrary.Generic (Arbitrary, arbitrary, shrink, genericArbitrary, genericShrink)
import GHC.Generics (Generic)
import Control.Monad (mzero)
import Data.Maybe (maybe, isJust)
import Control.Monad.State (StateT, runStateT, gets, modify)

-- type argument on Abs may not have any GTVars
data PrimValEnum = Plus   deriving (Show, Eq, Generic)
data PrimTypeEnum = IntT   deriving (Show, Eq, Generic)
data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Maybe Type) (Expr a) a | Let (Expr a) (Expr a) a | PrimInt Integer a | PrimVal PrimValEnum a  deriving (Show, Eq, Functor, Generic)
data Type = PrimT PrimTypeEnum | Fn Type Type | TVar Int | GTVar Int   deriving (Show, Eq, Generic)

instance Arbitrary PrimValEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary PrimTypeEnum where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance (Arbitrary a) => Arbitrary (Expr a) where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Type where
  arbitrary = genericArbitrary
  shrink = genericShrink

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

validAbsType :: Type -> Bool
validAbsType (PrimT _) = True
validAbsType (Fn a b) = validAbsType a && validAbsType b
validAbsType _ = False -- TODO what abt type variables?

validExpr' :: Int -> Expr () -> Bool
validExpr' n (EVar m ()) = m < n && m >= 0
validExpr' n (App a b ()) = validExpr' n a && validExpr' n b
validExpr' n (Abs t a ()) = maybe True validAbsType t && validExpr' (n+1) a
validExpr' n (Let a b ()) = validExpr' n a && validExpr' (n+1) b
validExpr' n (PrimInt _ ()) = True
validExpr' n (PrimVal _ ()) = True

validExpr :: Expr () -> Bool
validExpr = validExpr' 0

incVars :: Int -> Expr a -> Expr a
incVars n (EVar m q) | m >= n = EVar (m+1) q
incVars n (App x y q) = App (incVars n x) (incVars n y) q
incVars n (Abs t x q) = Abs t (incVars (n+1) x) q
incVars n (Let x y q) = Let (incVars n x) (incVars (n+1) y) q
incVars n x = x

replaceVar :: Int -> Expr a -> Expr a -> Expr a
replaceVar m a (EVar n _) | m == n = a
replaceVar m a (EVar n q) | m < n = EVar (n-1) q
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
hasTV n (GTVar m) = n == m
hasTV n (Fn a b) = hasTV n a || hasTV n b
hasTV _ _ = False

highestTypeVar :: Type -> Int
highestTypeVar (TVar n) = n
highestTypeVar (GTVar n) = n
highestTypeVar (Fn a b) = max (highestTypeVar a) (highestTypeVar b)
highestTypeVar _ = -1

intType :: Type
intType = PrimT IntT

typesAlphaEquiv :: Type -> Type -> StateT [(Int, Int)] Maybe ()
typesAlphaEquiv (GTVar n) (GTVar m) = typesAlphaEquiv (TVar n) (TVar m)
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
typesAlphaEquiv _ _ = mzero

runTypesAlphaEquiv :: Type -> Type -> Bool
runTypesAlphaEquiv a b = isJust $ runStateT (typesAlphaEquiv a b) []
