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

-- used in typeof to determine the types of vars and fnvals
data Env = Env { envVars :: [Type], envFns :: [(Int, Int, Type)], envStructs :: [(Int, Int)], maxTypeVar :: Int, maxLTVar :: Int } deriving (Eq, Show)

-- envVars should always be empty to start with since we don't start out inside a lambda
blankEnv :: ([(Int, Int, Type)], [(Int, Int)], Int, Int) -> Env
blankEnv (a,b,c,d) = Env [] a b c d

-- used when descending into lambda
pushEnvVar :: Type -> Env -> Env
pushEnvVar t env = env { envVars = t:(succType <$> envVars env) }

nthEnvFn :: Int -> [VarType] -> [LT] -> Env -> Maybe Type
nthEnvFn n vs ls env = do
  (vvs, lls, t) <- envFns env `atMay` n
  guard $ length vs == vvs
  guard $ length ls == lls
  replaceType vs ls t

typeIsMut :: Type -> Bool
typeIsMut (Type m _) = isMut m

isMut :: VarMut -> Bool
isMut Mut = True
isMut (Immut _) = False

-- shortest lifetime between two of them
minLT :: LT -> LT -> LT
minLT LTZero _ = LTZero
minLT _ LTZero = LTZero
minLT LTInf a = a
minLT a LTInf = a
minLT (LTSucc a) (LTSucc b) = LTSucc (minLT a b)
minLT a b = LTMin a b

-- min LT contained in a type
typeLT :: Type -> LT
typeLT (Type m t) = minLT (mutLT m) (varTypeLT t)

-- min LT contained in a vartype
varTypeLT :: VarType -> LT
varTypeLT (Struct _ ts ls) = foldr minLT LTInf $ ls <> (varTypeLT <$> ts)
varTypeLT (FnType _ l _ _) = l
varTypeLT _ = LTInf

-- min LT contained in a varmut
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

-- decs lifetimes, fails if there is an LTZero or an unsucced LTVar
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

-- all the free mutable vars in an expression; int is how deep we are below our starting point
freeMuts :: Int -> Env -> Expr -> S.Set Int
freeMuts n env (Lam _ a) = subtract 1 `S.map` freeMuts (n+1) env a
freeMuts n env (App a b) = (freeMuts n env a) `S.union` (freeMuts n env b)
freeMuts n env (Var m)
  | m < n || m >= n + length (envVars env) = S.empty
  | typeIsMut ((envVars env) !! (m - n)) = S.singleton m
  | otherwise = S.empty
freeMuts n env (FnVal _ _ _) = S.empty

-- min free LT in an expression; int is how deep we are below our starting point
-- specifically, the min LT of types of both mut and immut vars
minFreeLT :: Int -> Env -> Expr -> LT
minFreeLT n env (Lam t a) = succLT $ minFreeLT (n+1) env a
minFreeLT n env (App a b) = minLT (minFreeLT n env a) (minFreeLT n env a)
minFreeLT n env (Var m)
  | m < n || m >= n + length (envVars env) = LTInf
  | otherwise = typeLT $ (envVars env) !! (m - n)
minFreeLT n env (FnVal _ _ _) = LTInf

-- type of an expression, or nothing if it's not well-typed
typeof :: Env -> Expr -> Maybe Type
typeof env (Lam t0 a) = guard (checkType env $ vt t0) >> typeof newEnv a >>= f where
  f ta = pure $ Type Mut $ FnType once minLT t0 (succType ta)
  newEnv = pushEnvVar t0 env
  once = S.null (freeMuts 1 env a)
  minLT = minFreeLT 1 env a
typeof env (App a b) = do
  ta <- typeof env a
  tb <- typeof env b
  (ttb, tc) <- assertFnType ta
  guard $ S.null $ (freeMuts 0 env a) `S.intersection` (freeMuts 0 env b)
  guard $ tb == ttb
  pure tc
  where
    assertFnType (Type _ (FnType _ _ a b)) = pure (a, b)
    assertFnType _ = empty
typeof env (FnVal n vs ls) = guard (and $ checkType env <$> vs) >> nthEnvFn n vs ls env
typeof env (Var n) = (envVars env) `atMay` n

-- make sure a type is valid in a given environment
-- used in typeof
checkType :: Env -> VarType -> Bool
checkType env t = noInvalidStructsVarType (envStructs env) t && noTypeVarsAbove (maxTypeVar env) t && noLTVarsAboveVarType (maxLTVar env) t

-- make sure all structs have the right number of template arguments
noInvalidStructsType :: [(Int, Int)] -> Type -> Bool
noInvalidStructsType s (Type _ vt) = noInvalidStructsVarType s vt

noInvalidStructsVarType :: [(Int, Int)] -> VarType -> Bool
noInvalidStructsVarType s (Struct n vs ls) = n >= 0 && n < length s && length vs == fst (s !! n) && length ls == snd (s !! n) && and (noInvalidStructsVarType s <$> vs)
noInvalidStructsVarType s (FnType _ _ a b) = noInvalidStructsType s a && noInvalidStructsType s b
noInvalidStructsVarType _ _ = True

-- called by nthEnvFn, replaces type and lifetime template variables
-- like lambda substitution but at the type level
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

-- checks if an env is valid
-- assumes it was made by blankEnv, so envVars are ignored because they're assumed to be []
validEnv :: Env -> Bool
validEnv env = and (envFnValid (envStructs env) <$> envFns env) && and (envStructValid <$> envStructs env) && maxTypeVar env >= 0 && maxLTVar env >= 0

envFnValid :: [(Int, Int)] -> (Int, Int, Type) -> Bool
envFnValid s (v,l,t) = noInvalidStructsType s t && noTypeVarsAbove (v-1) (vt t) && noLTVarsAboveType l t && v >= 0 && l >= 0

envStructValid :: (Int, Int) -> Bool
envStructValid (v, l) = v >= 0 && l >= 0

-- makes sure all type vars are below a given threshold
noTypeVarsAbove :: Int -> VarType -> Bool
noTypeVarsAbove n (TypeVar m) = m <= n
noTypeVarsAbove n (Struct _ l _) = and $ noTypeVarsAbove n <$> l
noTypeVarsAbove n (FnType _ _ a b) = noTypeVarsAbove n (vt a) && noTypeVarsAbove n (vt b)
noTypeVarsAbove _ _ = True

-- makes sure all LT vars are below a given threshold
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

-- substitute variable n for a given expr
-- first expr arg is the thing to modify (the thing being called), second arg is the thing to put in (the fn argument)
callExpr :: Int -> Expr -> Expr -> Maybe Expr
callExpr n (Lam t a) b = Lam <$> (decType t) <*> (callExpr (n+1) a (succExpr b))
callExpr n (App a b) c = App <$> (callExpr n a c) <*> (callExpr n b c)
callExpr n (Var a) b
  | a == n = pure b
  | a > n  = pure $ Var (a+1)
  | otherwise = empty
callExpr _ a _ = pure a

-- simplify expr if possible
-- doesn't descend into lambdas
-- assumes the expr is well-typed (ie typeof returns Just _)
betaReduce :: Expr -> Maybe Expr
betaReduce (App (Lam t a) b) = callExpr 0 a b
betaReduce (App (App a b) c) = betaReduce (App a b) >>= betaReduce . flip App c
betaReduce a = pure a

-- checks for whnf
inNormalForm :: Expr -> Bool
inNormalForm (App (Lam _ _) _) = False
inNormalForm (App a@(App _ _) _) = inNormalForm a
inNormalForm _ = True

-- Arbitrary instances for quickchecking
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
  arbitrary = Env <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

--quickcheck tests

-- can't make type for this ugly term
toCheck1 (env,t) = let e = blankEnv env in not (validEnv e) || isNothing (typeof e (Lam t (App (Var 0) (Var 0))))
-- preservation
toCheck2 (env,expr) = let e = blankEnv env in not (validEnv e) || isNothing (typeof e expr) || ((betaReduce expr >>= typeof e) == typeof e expr)
-- progress
toCheck3 (env,expr) = let e = blankEnv env in not (validEnv e) || isNothing (typeof e expr) || inNormalForm expr || (betaReduce expr /= pure expr)
-- can make well typed terms (should fail)
toCheck4 (env,expr) = let e = blankEnv env in isNothing (typeof e expr)
-- can make non well typed terms (should fail)
toCheck5 (env,expr) = let e = blankEnv env in isJust (typeof e expr)

main = do
  putStrLn "testing unable to type \\a: T. a a"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 1000000} toCheck1
  putStrLn "testing preservation"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 1000000} toCheck2
  putStrLn "testing progress"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 1000000} toCheck3
  putStrLn "testing able to make well typed term (should fail)"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 1000000} toCheck4
  putStrLn "testing able to make badly typed term (should fail)"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 1000000} toCheck5
