import qualified Data.Set as S
import Safe
import Control.Monad
import Control.Applicative
import Data.Maybe
import Test.QuickCheck

-- uses de bruijn indexing for term-level variables and type-level LTs
-- uses named variables (named with ints rather than strings) for type and LT template vars, also for fns and structs
-- "LT" means lifetime
data Expr = Lam Type Expr | App Expr Expr | FnVal Int [VarType] [LT] | Var Int | PrimVal String Type deriving (Eq, Show)
data Type = Type { vm :: VarMut, vt :: VarType }                                                deriving (Eq, Show)
data VarType = TypeVar Int | Prim String | Struct Int [VarType] [LT] | FnType Bool LT Type Type deriving (Eq, Show) -- the bool in FnType means whether it's once or not
data VarMut = Mut | Immut LT                                                                    deriving (Eq, Show)
data LT = LTZero | LTSucc LT | LTMin LT LT | LTInf | LTVar Int                                  deriving (Eq, Show) -- LTZero means 'here, LTSucc means one level up, LTInf means 'static
data Code = Code { codeFns :: [(Int, Int, Expr, Type)], codeStructs :: [(Int, Int)] }           deriving (Eq, Show) -- codeFns and codeStructs ints are type and LT template vars; codeStructs really need more info
data Env = Env { envVars :: [Type], envFns :: [(Int, Int, Type)], envStructs :: [(Int, Int)], limTypeVar :: Int, limLTVar :: Int } deriving (Eq, Show) -- used in typeof to determine the types of vars and fnvals

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
succExpr (PrimVal a t) = PrimVal a (succType t)
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
typeof env (Lam t0 a) = guard (checkType env t0) >> typeof newEnv a >>= f where
  f ta = pure $ Type Mut $ FnType once minLT t0 ta
  newEnv = pushEnvVar t0 env
  once = not $ S.null (freeMuts 1 env a)
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
typeof env (FnVal n vs ls) = guard (and $ checkVarType env <$> vs) >> nthEnvFn n vs ls env
typeof env (Var n) = (envVars env) `atMay` n
typeof env (PrimVal _ t) = pure t

-- make sure a type is valid in a given environment
-- used in typeof
checkType :: Env -> Type -> Bool
checkType env t = noInvalidStructsVarType (envStructs env) (vt t) && noTypeVarsGeq (limTypeVar env) (vt t) && noLTVarsGeqType (limLTVar env) t

checkVarType :: Env -> VarType -> Bool
checkVarType env t = noInvalidStructsVarType (envStructs env) t && noTypeVarsGeq (limTypeVar env) t && noLTVarsGeqVarType (limLTVar env) t

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
validEnv env = and (envFnValid (envStructs env) <$> envFns env) && and (envStructValid <$> envStructs env) && limTypeVar env >= 0 && limLTVar env >= 0

envFnValid :: [(Int, Int)] -> (Int, Int, Type) -> Bool
envFnValid s (v,l,t) = noInvalidStructsType s t && noTypeVarsGeq v (vt t) && noLTVarsGeqType l t && v >= 0 && l >= 0

envStructValid :: (Int, Int) -> Bool
envStructValid (v, l) = v >= 0 && l >= 0

-- makes sure all type vars are below a given threshold
noTypeVarsGeq :: Int -> VarType -> Bool
noTypeVarsGeq n (TypeVar m) = m < n
noTypeVarsGeq n (Struct _ l _) = and $ noTypeVarsGeq n <$> l
noTypeVarsGeq n (FnType _ _ a b) = noTypeVarsGeq n (vt a) && noTypeVarsGeq n (vt b)
noTypeVarsGeq _ _ = True

-- makes sure all LT vars are below a given threshold
noLTVarsGeqType :: Int -> Type -> Bool
noLTVarsGeqType n t = noLTVarsGeqVarMut n (vm t) && noLTVarsGeqVarType n (vt t)

noLTVarsGeqVarType :: Int -> VarType -> Bool
noLTVarsGeqVarType n (Struct _ vs ls) = and (noLTVarsGeqVarType n <$> vs) && and (noLTVarsGeqLT n <$> ls)
noLTVarsGeqVarType n (FnType _ l a b) = noLTVarsGeqLT n l && noLTVarsGeqType n a && noLTVarsGeqType n b
noLTVarsGeqVarType _ _ = True

noLTVarsGeqVarMut :: Int -> VarMut -> Bool
noLTVarsGeqVarMut n Mut = True
noLTVarsGeqVarMut n (Immut l) = noLTVarsGeqLT n l

noLTVarsGeqLT :: Int -> LT -> Bool
noLTVarsGeqLT n (LTSucc a) = noLTVarsGeqLT n a
noLTVarsGeqLT n (LTMin a b) = noLTVarsGeqLT n a && noLTVarsGeqLT n b
noLTVarsGeqLT n (LTVar m) = m < n
noLTVarsGeqLT _ _ = True

-- substitute variable n for a given expr
-- first expr arg is the thing to modify (the thing being called), second arg is the thing to put in (the fn argument)
callExpr :: Int -> Expr -> Expr -> Maybe Expr
callExpr n (Lam t a) b = Lam <$> (decType t) <*> (callExpr (n+1) a (succExpr b))
callExpr n (App a b) c = App <$> (callExpr n a c) <*> (callExpr n b c)
callExpr n (Var a) b
  | a == n = pure b
  | a > n  = pure $ Var (a-1)
  | a < n  = pure $ Var a
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

checkCodeTypes :: Code -> Bool
checkCodeTypes code = and $ uncurry checkElem <$> codeToEnvs code `zip` codeFns code where
  checkElem env (_, _, e, t) = pure t == (typeof env e >>= modifyType)
  modifyType (Type _ t) = pure $ Type (Immut LTInf) t

codeToEnvs :: Code -> [Env]
codeToEnvs code = makeEnv <$> codeFns code where
  makeEnv (v,l,_,_) = generalEnv { limTypeVar = v, limLTVar = l }
  generalEnv = blankEnv (allTypes, codeStructs code, 0, 0)
  allTypes = makeTypeEntry <$> codeFns code
  makeTypeEntry (v,l,_,t) = (v,l,t)

-- count the occurrences of a in b
occurrences :: Expr -> Expr -> Int
occurrences a b | a == b = 1
occurrences a (Lam _ b) = occurrences a b
occurrences a (App b c) = occurrences a b + occurrences a c
occurrences a _ = 0

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
      pure (Prim ""),
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

instance Arbitrary Code where
  arbitrary = Code <$> arbitrary <*> arbitrary

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

toCheck6 (env,expr) = occurrences u expr > 0 || not (validEnv e) || isNothing (typeof e ex) || f (betaReduce ex) where
  e = blankEnv env
  u = PrimVal "uniqueVal" (Type Mut $ Prim "")
  ex = App expr u
  f Nothing = False
  f (Just a) = True -- occurrences u a <= 1

toCheck7 (env,expr) = occurrences u expr > 0 || not (validEnv e) || isNothing (typeof e ex) where
  e = blankEnv env
  u = PrimVal "uniqueVal" (Type Mut $ Prim "")
  ex = App expr u
  f Nothing = False
  f (Just a) = occurrences u a <= 1

exampleCode :: Code
exampleCode = Code { codeFns = fns, codeStructs = structs } where
  fns = [
      (1,1,Lam (Type (Immut (LTVar 0)) (TypeVar 0)) (Var 0),Type (Immut LTInf) (FnType False LTInf (Type (Immut (LTVar 0)) (TypeVar 0)) (Type (Immut (LTVar 0)) (TypeVar 0)))),
      (0,0,FnVal 0 [Prim "int"] [LTInf], Type (Immut LTInf) (FnType False LTInf (Type (Immut LTInf) (Prim "int")) (Type (Immut LTInf) (Prim "int"))))
    ]
  structs = []

main = do
  putStrLn "Type check on example code (should be True):"
  print $ checkCodeTypes exampleCode
  putStrLn "testing unable to type \\a: T. a a"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck1
  putStrLn "testing preservation"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck2
  putStrLn "testing progress"
  quickCheckWith stdArgs{maxSize = 5, maxSuccess = 100000} toCheck3
  putStrLn "testing able to make well typed term (should fail)"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 100000} toCheck4
  putStrLn "testing able to make badly typed term (should fail)"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 100000} toCheck5
  putStrLn "testing able to make term that accepts unique val (should fail)"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 1000000} toCheck7
  putStrLn "muts can't be duplicated"
  quickCheckWith stdArgs{maxSize = 1, maxSuccess = 1000000} toCheck6
