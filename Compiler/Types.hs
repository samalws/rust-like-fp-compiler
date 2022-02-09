{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module Compiler.Types where

import Prelude hiding (abs)
import GHC.Generics (Generic)
import Control.Monad (mzero, replicateM)
import Data.Tuple.Extra ((***))
import Data.Maybe (maybe, isJust, fromJust, fromMaybe)
import Data.Set (Set, singleton, empty)
import qualified Data.Set as Set
import Control.Monad.State (StateT, runStateT, gets, modify)

data PrimOpEnum = Plus | Tup | IfZ   deriving (Show, Eq, Generic)
data PrimTypeEnum = IntT   deriving (Show, Eq, Generic)
data Expr a = EVar Int a | App (Expr a) (Expr a) a | Abs (Maybe Type) (Expr a) a | Let (Expr a) (Expr a) a | PrimInt Integer a | TupAccess Int Int (Expr a) a | PrimOp PrimOpEnum [Expr a] a | FnVal Int a  deriving (Show, Eq, Functor, Generic)
data Type = PrimT PrimTypeEnum | TupT [Type] | Fn Type Type | TVar Int   deriving (Show, Eq, Generic)
newtype Code a = Code [(Type, Expr a)] deriving (Eq, Show, Generic)
type Register = Int

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
validExpr' maxFn n (FnVal m ()) = m >= 0 && m < maxFn

validExpr :: Int -> Expr () -> Bool
validExpr maxFn = validExpr' maxFn 0

validCode :: Code () -> Bool
validCode (Code l) = all (validExpr ll . snd) l where ll = length l

incVars :: Int -> Expr a -> Expr a
incVars n (EVar m q) | m >= n = EVar (m+1) q
incVars n (App x y q) = App (incVars n x) (incVars n y) q
incVars n (Abs t x q) = Abs t (incVars (n+1) x) q
incVars n (Let x y q) = Let (incVars n x) (incVars (n+1) y) q
incVars n (TupAccess nn m a q) = TupAccess nn m (incVars n a) q
incVars n (PrimOp a l q) = PrimOp a (incVars n <$> l) q
incVars n x = x

replaceVar :: Bool -> Int -> Expr a -> Expr a -> Expr a
replaceVar i m a (EVar n _) | m == n = a
replaceVar i m a (EVar n q) | i && m < n = EVar (n-1) q
replaceVar i m a (App x y q) = App (replaceVar i m a x) (replaceVar i m a y) q
replaceVar i m a (Abs t x q) = Abs t (replaceVar i (m+1) (incVars 0 a) x) q
replaceVar i m a (Let x y q) = Let (replaceVar i m a x) (replaceVar i (m+1) (incVars 0 a) y) q
replaceVar i m a (TupAccess n mm x q) = TupAccess n mm (replaceVar i m a x) q
replaceVar i m a (PrimOp o l q) = PrimOp o (replaceVar i m a <$> l) q
replaceVar _ _ _ x = x

replaceVars :: [(Int,Expr a)] -> Expr a -> Expr a
replaceVars m (EVar n q) = fromMaybe (EVar n q) $ lookup n m
replaceVars m (App x y q) = App (replaceVars m x) (replaceVars m y) q
replaceVars m (Abs t x q) = Abs t (replaceVars (((+1) *** incVars 0) <$> m) x) q
replaceVars m (Let x y q) = Let (replaceVars m x) (replaceVars (((+1) *** incVars 0) <$> m) y) q
replaceVars m (TupAccess n mm x q) = TupAccess n mm (replaceVars m x) q
replaceVars m (PrimOp o l q) = PrimOp o (replaceVars m <$> l) q
replaceVars _ x = x

decVarSet :: Set Int -> Set Int
decVarSet = Set.map (subtract 1) . Set.delete 0

freeVars :: Expr a -> Set Int
freeVars (EVar n _) = singleton n
freeVars (App x y q) = freeVars x <> freeVars y
freeVars (Abs t x q) = decVarSet $ freeVars x
freeVars (Let x y q) = freeVars x <> decVarSet (freeVars y)
freeVars (TupAccess n mm x q) = freeVars x
freeVars (PrimOp o l q) = foldMap freeVars l
freeVars x = empty

replaceFns :: [(Int, Int)] -> Expr a -> Expr a
replaceFns m (FnVal n q) = FnVal (fromJust $ lookup n m) q
replaceFns m (App x y q) = App (replaceFns m x) (replaceFns m y) q
replaceFns m (Abs t x q) = Abs t (replaceFns m x) q
replaceFns m (Let x y q) = Let (replaceFns m x) (replaceFns m y) q
replaceFns m (TupAccess n mm x q) = TupAccess n mm (replaceFns m x) q
replaceFns m (PrimOp o l q) = PrimOp o (replaceFns m <$> l) q
replaceFns _ x = x

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

typesAlphaEquivMapping :: Type -> Type -> Maybe [(Int,Int)]
typesAlphaEquivMapping a b = snd <$> runStateT (typesAlphaEquiv a b) []
