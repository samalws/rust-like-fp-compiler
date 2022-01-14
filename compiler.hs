{-# LANGUAGE TupleSections #-}

import Control.Monad.State.Lazy (State, modify, runState, execState, get, put)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.Set (Set, empty, singleton, fromList, toList)
import Data.Maybe (mapMaybe, fromJust)
import Data.Tuple.HT (mapFst)

-- Just n - by, or Nothing if that would be negative
decN :: Int -> Int -> Maybe Int
decN by n = if (n < by) then Nothing else Just (n - by)

-- mapMaybe over set elements
setMapMaybe :: (Ord b) => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f = fromList . mapMaybe f . toList

type Reg = Int
type MReg = Maybe Reg
type MRC = (MReg, Cont)
data IoEnum = Print                           deriving (Show, Read, Eq, Ord)
data CmpEnum = Eq | Neq | Leq | Geq | Lt | Gt deriving (Show, Read, Eq, Ord)
data ArithEnum = Add | Mul                    deriving (Show, Read, Eq, Ord)
data Val = Var !Int | Reg !Reg | Lit !Int | Label !Int | Get !Val !Val -- in Get, first arg is the index
                                              deriving (Show, Read, Eq, Ord)
data Cont = Io !IoEnum ![Val] ![MReg] !Cont
          | Cmp !CmpEnum !Val !Val !Cont !Cont !Cont
          | Arith !ArithEnum !Val !Val !MRC
          | Let !Val !MRC
          | Lambda ![MReg] !Cont !MRC
          | Struct ![Val] !MRC
          | Call !Val ![(MReg, Val)]
          | Dealloc !(Either [Int] Int) !Cont
          deriving (Show, Read, Eq, Ord)
type CodeFn = (Either Int [Reg], Cont)
data Code = Code { codeFns :: ![CodeFn], codeMain :: !Int } deriving (Show, Read, Eq, Ord)
data Asm = LBL Int
         | ARITHREG ArithEnum Reg Reg
         | ARITHLIT ArithEnum Reg Int
         | MOVRAM Reg Reg Int
         | MOVREG Reg Reg
         | MOVLIT Reg Int
         | JMP Int
         | CMP Reg Reg -- TODO what abt compare lits
         | JMPCND CmpEnum Int
         | PSHREG Reg
         | PSHLIT Int
         | POPN Int
         | IOASM IoEnum [Reg] [Reg]
         deriving (Show, Read, Eq, Ord)

spReg :: Reg
spReg = 0 -- TODO

valToReg :: Val -> Reg
valToReg (Reg n) = n

-- I almost just rediscovered van laarhoven lenses
modifySubcontsM :: (Applicative m) => (Cont -> m Cont) -> Cont -> m Cont
modifySubcontsM f (Io a b c x) = Io a b c <$> f x
modifySubcontsM f (Cmp a b c x y z) = Cmp a b c <$> f x <*> f y <*> f z
modifySubcontsM f (Arith a b c (d, x)) = Arith a b c . (d,) <$> f x
modifySubcontsM f (Let a (b, x)) = Let a . (b,) <$> f x
modifySubcontsM f (Lambda a x (b, y)) = Lambda a <$> f x <*> ((b,) <$> f y)
modifySubcontsM f (Struct a (b, x)) = Struct a . (b,) <$> f x
modifySubcontsM f (Dealloc a x) = Dealloc a <$> f x
modifySubcontsM _ a = pure a

modifySubconts :: (Cont -> Cont) -> Cont -> Cont
modifySubconts f = runIdentity . modifySubcontsM (Identity . f)

getSubconts :: Cont -> [Cont]
getSubconts cont = execState (modifySubcontsM f cont) [] where
  f :: Cont -> State [Cont] Cont
  f c = modify ( c: ) >> pure c -- c: C: ;-;

-- num of vars created for each subcont
-- NOTE: breaks when dealloc is involved
varsCreated :: Cont -> [Int]
varsCreated (Io Print _ _ _) = [0]
varsCreated (Cmp{}) = [0,0,0]
varsCreated (Call{}) = []
varsCreated (Dealloc{}) = undefined
varsCreated _  = [1]

-- vals referenced in a cont
-- does not do recursively
-- NOTE: breaks when dealloc is involved
valsUsed :: Cont -> [Val]
valsUsed (Io _ vs _ _) = vs
valsUsed (Cmp _ va vb _ _ _) = [va,vb]
valsUsed (Arith _ va vb _) = [va,vb]
valsUsed (Let v _) = [v]
valsUsed (Lambda{}) = []
valsUsed (Struct vs _) = vs
valsUsed (Call v vs) = v : (snd <$> vs)
valsUsed (Dealloc{}) = undefined

-- valsUsed, but only the Vars
varsUsed :: Cont -> [Int]
varsUsed c = mapMaybe f $ valsUsed c where
  f (Var n) = Just n
  f _ = Nothing

-- all free vars in a cont
-- NOTE: breaks when dealloc is involved
freeVars :: Cont -> Set Int
freeVars cont = fromList (varsUsed cont) <> mconcat ((\(c, n) -> setMapMaybe (decN n) $ freeVars c) <$> zip (getSubconts cont) (varsCreated cont))

-- STAGES:
--   1. closure convert, code should now have no Lambdas in it
--   ?. stack decrement, now every Alloc should be matched with a Dealloc
--   ?. explicit Gets, now Gets should only be present in Lets, and Gets should only be nested one deep and should only get Lits not vars
--   ?. register spilling, now the number of free variables should be < n everywhere in the code
--   ?. register allocation, now there should be no Vars present in the code
--   ?. use of accumulator register, now all Arith expressions should have first variable == result register
--   100. assembly generation

-- STAGE 1 - CLOSURE CONVERSION --

-- remove Lambdas, replacing with Struct calls
-- adds new fns to the Code using mkFn
closureConvert' :: (CodeFn -> State a Int) -> Cont -> State a Cont
closureConvert' mkFn l@(Lambda{}) = do
  newL <- modifySubcontsM (closureConvert' mkFn) l
  case newL of
    Lambda a fnBody rest -> do
      let bodyFree = freeVars fnBody
      let newBody = fnBody -- TODO
      n <- mkFn (Left (length a), newBody)
      let newRest = rest -- TODO
      pure $ Lambda a newBody newRest
    _ -> error "modifySubcontsM changed ctor"
closureConvert' mkFn a@(Call (Label _) _) = pure a
closureConvert' mkFn (Call f args) = pure $ Call (Get (Lit 0) f) ((Nothing, Get (Lit 1) f):args)
closureConvert' mkFn a = modifySubcontsM (closureConvert' mkFn) a

-- remove Lambdas, replacing with Struct calls
-- uses closureConvert' as a helper method
closureConvert :: Code -> Code
closureConvert c = c { codeFns = f $ runState st (length fns, []) } where
  fns :: [CodeFn]
  fns = codeFns c
  f :: ([a], (t, [a])) -> [a]
  f (x, (_, y)) = x <> y
  st :: State (Int, [CodeFn]) [CodeFn]
  st = sequence $ map convertIndividual fns
  convertIndividual :: CodeFn -> State (Int, [CodeFn]) CodeFn
  convertIndividual (a, c) = (a,) <$> closureConvert' appendFn c
  appendFn :: a -> State (Int, [a]) Int
  appendFn f = do
    (n, fs) <- get
    put (n+1, f:fs)
    pure n

-- STAGE 100 - ASSEMBLY GENERATION --

-- functions provided: add instruction, add LBL, convert Label to LBL
genAsm' :: (Asm -> State a ()) -> State a Int -> (Int -> Int) -> Cont -> State a ()
genAsm' ai al cl (Io i as bs r) = do
  ai $ IOASM i (valToReg <$> as) (fromJust <$> bs)
  genAsm' ai al cl r
genAsm' ai al cl (Cmp c va vb t f r) = do
  l1 <- al
  l2 <- al
  ai $ CMP (valToReg va) (valToReg vb) -- TODO add option for lits, at least in b
  ai $ JMPCND c l1
  genAsm' ai al cl f
  ai $ JMP l2
  ai $ LBL l1
  genAsm' ai al cl t
  ai $ LBL l2
  genAsm' ai al cl r
genAsm' ai al cl (Arith a (Reg va) (Reg vb) (_, r)) = do
  ai $ ARITHREG a va vb
  genAsm' ai al cl r
genAsm' ai al cl (Arith a (Reg va) (Lit vb) (_, r)) = do
  ai $ ARITHLIT a va vb
  genAsm' ai al cl r
genAsm' ai al cl (Let (Reg a) (b, r)) = do
  ai $ MOVREG (fromJust b) a
  genAsm' ai al cl r
genAsm' ai al cl (Let (Lit a) (b, r)) = do
  ai $ MOVLIT (fromJust b) a
  genAsm' ai al cl r
genAsm' ai al cl (Let (Get (Reg a) (Lit n)) (b, r)) = do
  ai $ MOVRAM (fromJust b) a n
  genAsm' ai al cl r
genAsm' ai al cl (Struct vs (b, r)) = do
  sequence $ ai . pshFun <$> vs -- TODO reverse order??
  ai $ MOVREG (fromJust b) spReg -- TODO add a certain amount?
  genAsm' ai al cl r
  where
    pshFun (Reg a) = PSHREG a
    pshFun (Lit a) = PSHLIT a
genAsm' ai al cl (Call (Label f) vs) = do
  -- TODO how to assign vs without musical chairs
  ai $ JMP (cl f)
genAsm' ai al cl (Call (Reg f) vs) = do
  -- TODO how to assign vs without musical chairs
  ai $ JMP f
genAsm' ai al cl (Dealloc (Right n) r) = do
  ai $ POPN n
  genAsm' ai al cl r

-- functions provided: add instruction, add LBL, convert Label to LBL
genAsm'Code :: (Asm -> State a ()) -> (Maybe Int -> State a Int) -> (Int -> Int) -> Code -> State a Int
genAsm'Code ai al cl code = (sequence $ map genFn (codeFns code)) >> pure (cl (codeMain code)) where
  genFn (_, c) = genAsm' ai (al Nothing) cl c

genAsm :: Code -> [Asm]
genAsm code = reverse asm where
  (asm, lbls) = execState (genAsm'Code ai al cl code) ([], [])
  ai :: Asm -> State ([Asm], [(Maybe Int, Int)]) ()
  ai x = modify (mapFst (x:))
  al :: Maybe Int -> State ([Asm], [(Maybe Int, Int)]) Int
  al x = do
    (a,l) <- get
    let ll = length l
    put (a, ((x,ll):l))
    pure ll
  cl :: Int -> Int
  cl x = fromJust $ lookup (Just x) lbls -- this can be done because of lazy evaluation, similar to tardis monad

main = pure ()
