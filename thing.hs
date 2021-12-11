import qualified Data.Set as S
import Safe
import Control.Monad
import Control.Applicative
import Data.Maybe
import Test.QuickCheck

data Expr = Lam Type Expr | App Expr Expr | FnVal Int [VarType] [LT] | Var Int                  deriving (Eq, Show)
data Type = Type VarMut VarType                                                                 deriving (Eq, Show)
data VarType = TypeVar Int | Prim String | Struct Int [VarType] [LT] | FnType Bool LT Type Type deriving (Eq, Show)
data VarMut = Mut | Immut LT                                                                    deriving (Eq, Show)
data LT = LTZero | LTSucc LT | LTMin LT LT | LTInf | LTVar Int                                  deriving (Eq, Show)

-- TODO is there an expr env
data TypeEnv = TypeEnv { envVars :: [Type], envFns :: [[VarType] -> [LT] -> Maybe Type] }
pushTypeEnvVar :: Type -> TypeEnv -> TypeEnv
pushTypeEnvVar t env = env { envVars = t:(succType <$> envVars env) }

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

instance Arbitrary TypeEnv where
  arbitrary = (flip TypeEnv []) <$> arbitrary -- TODO

instance Show TypeEnv where
  show (TypeEnv a b) = "TypeEnv " <> show a <> " []" -- TODO

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

freeMuts :: Int -> TypeEnv -> Expr -> S.Set Int
freeMuts n env (Lam _ a) = subtract 1 `S.map` freeMuts (n+1) env a
freeMuts n env (App a b) = (freeMuts n env a) `S.union` (freeMuts n env b)
freeMuts n env (Var m)
  | m < n || m >= n + length (envVars env) = S.empty
  | typeIsMut ((envVars env) !! (m - n)) = S.singleton m
  | otherwise = S.empty
freeMuts n env (FnVal _ _ _) = S.empty

minFreeLT :: Int -> TypeEnv -> Expr -> LT
minFreeLT n env (Lam t a) = succLT $ minFreeLT (n+1) env a
minFreeLT n env (App a b) = minLT (minFreeLT n env a) (minFreeLT n env a)
minFreeLT n env (Var m)
  | m < n || m >= n + length (envVars env) = LTInf
  | otherwise = typeLT $ (envVars env) !! (m - n)
minFreeLT n env (FnVal _ _ _) = LTInf

checkType :: TypeEnv -> Expr -> Maybe Type
checkType env (Lam t0 a) = checkType newTypeEnv a >>= f where
  f ta = pure $ Type Mut $ FnType once minLT t0 (succType ta)
  newTypeEnv = pushTypeEnvVar t0 env
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
checkType env (FnVal n vs ls) = ((envFns env) `atMay` n) >>= (($ ls) . ($ vs))
checkType env (Var n) = (envVars env) `atMay` n

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

betaReduceInsideLam :: Expr -> Maybe Expr
betaReduceInsideLam (Lam t a) = Lam t <$> betaReduceInsideLam a
betaReduceInsideLam a = betaReduce a

-- can't make type for this ugly term
toCheck1 t = isNothing $ checkType (TypeEnv [] []) (Lam t (App (Var 0) (Var 0)))
-- preservation
toCheck2 (env,expr) = isNothing (checkType env expr) || ((betaReduce expr >>= checkType env) == checkType env expr)
-- preservation for betaReduceInsideLam
toCheck3 (env,expr) = isNothing (checkType env expr) || ((betaReduceInsideLam expr >>= checkType env) == checkType env expr)
-- progress
toCheck4 (env,expr) = isNothing (checkType env expr) || inNormalForm expr || (betaReduce expr /= pure expr)
-- can make well typed terms (should fail)
toCheck5 (env,expr) = isNothing (checkType env expr)

main = pure ()
