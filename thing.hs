import qualified Data.Set as S
import Safe
import Control.Monad
import Control.Applicative
import Data.Maybe
import Test.QuickCheck

data Expr = Lam Type Expr | App Expr Expr | FnVal Int [VarType] [LT] | Var Int                  deriving (Eq, Show)
data Type = Type { vm :: VarMut, vt :: VarType }                                                deriving (Eq, Show)
data VarType = TypeVar Int | Prim String | Struct Int [VarType] [LT] | FnType Bool LT Type Type deriving (Eq, Show)
data VarMut = Mut | Immut LT                                                                    deriving (Eq, Show)
data LT = LTZero | LTSucc LT | LTMin LT LT | LTInf | LTVar Int                                  deriving (Eq, Show)

-- used in typechecking to determine the types of vars and fnvals
data Env = Env { envVars :: [Type], envFns :: [(Int, Int, Type)] }
blankEnv :: [(Int, Int, Type)] -> Env
blankEnv = Env []
pushEnvVar :: Type -> Env -> Env
pushEnvVar t env = env { envVars = t:(succType <$> envVars env) }
nthEnvFn :: Int -> [VarType] -> [LT] -> Env -> Maybe Type
nthEnvFn n vs ls env = do
  (vvs, lls, t) <- envFns env `atMay` n
  guard $ length vs == vvs
  guard $ length ls == lls
  replaceType vs ls t

instance Arbitrary Expr where
  arbitrary = oneof [
      Lam <$> arbitrary <*> arbitrary,
      App <$> arbitrary <*> arbitrary,
      FnVal <$> arbitrary <*> arbitrary <*> arbitrary,
      Var <$> arbitrary
    ]

instance Arbitrary Type where
  arbitrary = Type <$> arbitrary <*> arbitrary

instance Arbitrary VarType where
  arbitrary = oneof [
      TypeVar <$> arbitrary,
      Prim <$> arbitrary,
      Struct <$> arbitrary <*> arbitrary <*> arbitrary,
      FnType <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    ]

instance Arbitrary VarMut where
  arbitrary = oneof [
      pure Mut,
      Immut <$> arbitrary
    ]

instance Arbitrary LT where
  arbitrary = oneof [
      pure LTZero,
      LTSucc <$> arbitrary,
      LTMin <$> arbitrary <*> arbitrary,
      pure LTInf,
      LTVar <$> arbitrary
    ]

instance Arbitrary Env where
  arbitrary = Env <$> arbitrary <*> arbitrary

instance Show Env where
  show (Env a b) = "Env " <> show a <> " []" -- TODO

typeIsMut :: Type -> Bool
typeIsMut (Type m _) = isMut m

isMut :: VarMut -> Bool
isMut Mut = True
isMut (Immut _) = False

minLT :: LT -> LT -> LT
minLT LTZero _ = LTZero
minLT _ LTZero = LTZero
minLT LTInf a = a
minLT a LTInf = a
minLT (LTSucc a) (LTSucc b) = LTSucc (minLT a b)
minLT a b = LTMin a b

typeLT :: Type -> LT
typeLT (Type m t) = minLT (mutLT m) (varTypeLT t)

varTypeLT :: VarType -> LT
varTypeLT (Struct _ ts ls) = foldr minLT LTInf $ ls <> (varTypeLT <$> ts)
varTypeLT (FnType _ l _ _) = l
varTypeLT _ = LTInf

mutLT :: VarMut -> LT
mutLT Mut = LTInf
mutLT (Immut l) = l

-- succs lifetimes
succType :: Type -> Type
succType (Type a b) = Type (succVarMut a) (succVarType b)

succVarType :: VarType -> VarType
succVarType (Struct n ts ls) = Struct n (succVarType <$> ts) (succLT <$> ls)
succVarType (FnType b l ta tb) = FnType b (succLT l) (succType ta) (succType tb)
succVarType a = a -- what about typevar?

succVarMut :: VarMut -> VarMut
succVarMut Mut = Mut
succVarMut (Immut l) = Immut (succLT l)

succLT :: LT -> LT
succLT (LTMin a b) = LTMin (succLT a) (succLT b)
succLT LTInf = LTInf
succLT l = LTSucc l

-- succs vars and types
succExpr :: Expr -> Expr
succExpr (Lam t a) = Lam (succType t) (succExpr a)
succExpr (App a b) = App (succExpr a) (succExpr b)
succExpr (Var a) = Var (a+1)
succExpr a = a

-- decs lifetimes
decType :: Type -> Maybe Type
decType (Type a b) = do
  da <- decVarMut a
  db <- decVarType b
  pure $ Type da db

decVarType :: VarType -> Maybe VarType
decVarType (Struct n ts ls) = do
  dts <- sequence $ decVarType <$> ts
  dls <- sequence $ decLT <$> ls
  pure $ Struct n dts dls
decVarType (FnType b l ta tb) = do
  dl  <- decLT l
  dta <- decType ta
  dtb <- decType tb
  pure $ FnType b dl dta dtb
decVarType a = pure a

decVarMut :: VarMut -> Maybe VarMut
decVarMut Mut = pure Mut
decVarMut (Immut l) = Immut <$> decLT l

decLT :: LT -> Maybe LT
decLT (LTMin a b) = do
  da <- decLT a
  db <- decLT b
  pure $ LTMin da db
decLT LTInf = pure LTInf
-- these 2 lines are the ones that really matter here
decLT (LTSucc l) = pure l
decLT _ = empty

freeMuts :: Int -> Env -> Expr -> S.Set Int
freeMuts n env (Lam _ a) = subtract 1 `S.map` freeMuts (n+1) env a
freeMuts n env (App a b) = (freeMuts n env a) `S.union` (freeMuts n env b)
freeMuts n env (Var m)
  | m < n || m >= n + length (envVars env) = S.empty
  | typeIsMut ((envVars env) !! (m - n)) = S.singleton m
  | otherwise = S.empty
freeMuts n env (FnVal _ _ _) = S.empty

minFreeLT :: Int -> Env -> Expr -> LT
minFreeLT n env (Lam t a) = succLT $ minFreeLT (n+1) env a
minFreeLT n env (App a b) = minLT (minFreeLT n env a) (minFreeLT n env a)
minFreeLT n env (Var m)
  | m < n || m >= n + length (envVars env) = LTInf
  | otherwise = typeLT $ (envVars env) !! (m - n)
minFreeLT n env (FnVal _ _ _) = LTInf

checkType :: Env -> Expr -> Maybe Type
checkType env (Lam t0 a) = checkType newEnv a >>= f where
  f ta = pure $ Type Mut $ FnType once minLT t0 (succType ta)
  newEnv = pushEnvVar t0 env
  once = S.null (freeMuts 1 env a)
  minLT = minFreeLT 1 env a
checkType env (App a b) = do
  ta <- checkType env a
  tb <- checkType env b
  (ttb, tc) <- assertFnType ta
  guard $ S.null $ (freeMuts 0 env a) `S.intersection` (freeMuts 0 env b)
  guard $ tb == ttb
  pure tc
  where
    assertFnType (Type _ (FnType _ _ a b)) = pure (a, b)
    assertFnType _ = empty
checkType env (FnVal n vs ls) = nthEnvFn n vs ls env
checkType env (Var n) = (envVars env) `atMay` n

-- called by nthEnvFn, replaces template and lifetime variables
replaceType :: [VarType] -> [LT] -> Type -> Maybe Type
replaceType vs ls (Type m t) = Type <$> replaceVarMut ls m <*> replaceVarType vs ls t

replaceVarType :: [VarType] -> [LT] -> VarType -> Maybe VarType
replaceVarType vs ls (TypeVar n) = vs `atMay` n
replaceVarType vs ls (Struct n vvs lls) = Struct n <$> (sequence $ replaceVarType vs ls <$> vvs) <*> (sequence $ replaceLT ls <$> lls)
replaceVarType vs ls (FnType o l a b) = FnType o <$> (replaceLT ls l) <*> (replaceType vs ls a) <*> (replaceType vs ls b)
replaceVarType vs ls a = pure a

replaceVarMut :: [LT] -> VarMut -> Maybe VarMut
replaceVarMut ls Mut = pure Mut
replaceVarMut ls (Immut l) = Immut <$> replaceLT ls l

replaceLT :: [LT] -> LT -> Maybe LT
replaceLT ls (LTSucc l) = LTSucc <$> replaceLT ls l
replaceLT ls (LTMin a b) = LTMin <$> replaceLT ls a <*> replaceLT ls b
replaceLT ls (LTVar n) = ls `atMay` n
replaceLT ls a = pure a

validEnv :: Env -> Bool
validEnv env = and (envFnValid <$> envFns env)

envFnValid :: (Int, Int, Type) -> Bool
envFnValid (v,l,t) = noTypeVarsAbove (v-1) (vt t) && noLTVarsAboveType l t

{-
data Type = Type { vm :: VarMut, vt :: VarType }                                                deriving (Eq, Show)
data VarType = TypeVar Int | Prim String | Struct Int [VarType] [LT] | FnType Bool LT Type Type deriving (Eq, Show)
data VarMut = Mut | Immut LT                                                                    deriving (Eq, Show)
data LT = LTZero | LTSucc LT | LTMin LT LT | LTInf | LTVar Int                                  deriving (Eq, Show)
-}

noTypeVarsAbove :: Int -> VarType -> Bool
noTypeVarsAbove n (TypeVar m) = m <= n
noTypeVarsAbove n (Struct _ l _) = and $ noTypeVarsAbove n <$> l
noTypeVarsAbove n (FnType _ _ a b) = noTypeVarsAbove n (vt a) && noTypeVarsAbove n (vt b)
noTypeVarsAbove _ _ = True

noLTVarsAboveType :: Int -> Type -> Bool
noLTVarsAboveType n t = noLTVarsAboveVarMut n (vm t) && noLTVarsAboveVarType n (vt t)

noLTVarsAboveVarType :: Int -> VarType -> Bool
noLTVarsAboveVarType n (Struct _ vs ls) = and (noLTVarsAboveVarType n <$> vs) && and (noLTVarsAboveLT n <$> ls)
noLTVarsAboveVarType n (FnType _ l a b) = noLTVarsAboveLT n l && noLTVarsAboveType n a && noLTVarsAboveType n b
noLTVarsAboveVarType _ _ = True

noLTVarsAboveVarMut :: Int -> VarMut -> Bool
noLTVarsAboveVarMut n Mut = True
noLTVarsAboveVarMut n (Immut l) = noLTVarsAboveLT n l

noLTVarsAboveLT :: Int -> LT -> Bool
noLTVarsAboveLT n (LTSucc a) = noLTVarsAboveLT n a
noLTVarsAboveLT n (LTMin a b) = noLTVarsAboveLT n a && noLTVarsAboveLT n b
noLTVarsAboveLT n (LTVar m) = m <= n
noLTVarsAboveLT _ _ = True

callExpr :: Int -> Expr -> Expr -> Maybe Expr
callExpr n (Lam t a) b = Lam <$> (decType t) <*> (callExpr (n+1) a (succExpr b))
callExpr n (App a b) c = App <$> (callExpr n a c) <*> (callExpr n b c)
callExpr n (Var a) b
  | a == n = pure b
  | a > n  = pure $ Var (a+1)
  | otherwise = empty
callExpr _ a _ = pure a

betaReduce :: Expr -> Maybe Expr
betaReduce (App (Lam t a) b) = callExpr 0 a b
betaReduce (App (App a b) c) = betaReduce (App a b) >>= betaReduce . flip App c
betaReduce a = pure a

inNormalForm :: Expr -> Bool
inNormalForm (App (Lam _ _) _) = False
inNormalForm (App a@(App _ _) _) = inNormalForm a
inNormalForm _ = True

-- can't make type for this ugly term
toCheck1 (env,t) = let e = blankEnv env in not (validEnv e) || isNothing (checkType e (Lam t (App (Var 0) (Var 0))))
-- preservation
toCheck2 (env,expr) = let e = blankEnv env in not (validEnv e) || isNothing (checkType e expr) || ((betaReduce expr >>= checkType e) == checkType e expr)
-- progress
toCheck3 (env,expr) = let e = blankEnv env in not (validEnv e) || isNothing (checkType e expr) || inNormalForm expr || (betaReduce expr /= pure expr)
-- can make well typed terms (should fail)
toCheck4 (env,expr) = let e = blankEnv env in isNothing (checkType e expr)
-- can make non well typed terms (should fail)
toCheck5 (env,expr) = let e = blankEnv env in isJust (checkType e expr)

main = do
  -- TODO if I make it 6, it gets stuck sometimes
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck1
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck2
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck3
  putStrLn "next one should fail"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 100000} toCheck4
  putStrLn "next one should fail"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 100000} toCheck5
