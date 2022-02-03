{-# LANGUAGE DeriveFunctor #-}

module Compiler.Types where

import Prelude hiding (abs)

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
hasTV n (Fn a b) = hasTV n a || hasTV n b
hasTV _ _ = False

intType :: Type
intType = PrimT "int"
