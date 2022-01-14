{-# LANGUAGE TupleSections #-}

import Control.Monad.State.Strict (State, modify, runState, execState, get, put)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.Set (Set, empty, singleton, fromList, toList)
import Data.Maybe (mapMaybe)

-- Just n - by, or Nothing if that would be negative
decN :: Int -> Int -> Maybe Int
decN by n = if (n < by) then Nothing else Just (n - by)

-- mapMaybe over set elements
setMapMaybe :: (Ord b) => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f = fromList . mapMaybe f . toList

type Reg = Int
type MReg = Maybe Reg
type MRC = (MReg, Cont)
data IoEnum = Print                     deriving (Show, Read, Eq, Ord)
data CmpEnum = Eq | Leq | Geq | Lt | Gt deriving (Show, Read, Eq, Ord)
data ArithEnum = Add | Mul              deriving (Show, Read, Eq, Ord)
data Val = Var !Int | Reg !Reg | Lit !Int | Label !Int | Get !Val !Val -- in Get, first arg is the index
                                        deriving (Show, Read, Eq, Ord)
data Cont = Io !IoEnum ![Val] ![MReg] !Cont
          | Cmp !CmpEnum !Val !Val !Cont !Cont
          | Arith !ArithEnum !Val !Val !MRC
          | Let !Val !MRC
          | Lambda ![MReg] !Cont !MRC
          | Struct ![Val] !MRC
          | Call !Val ![(MReg, Val)]
          | Dealloc !(Either [Int] Int) !Cont
          deriving (Show, Read, Eq, Ord)
type CodeFn = (Either Int [Reg], Cont)
data Code = Code { codeFns :: ![CodeFn], codeMain :: !Int } deriving (Show, Read, Eq, Ord)

-- I almost just rediscovered van laarhoven lenses
modifySubcontsM :: (Applicative m) => (Cont -> m Cont) -> Cont -> m Cont
modifySubcontsM f (Io a b c x) = Io a b c <$> f x
modifySubcontsM f (Cmp a b c x y) = Cmp a b c <$> f x <*> f y
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
varsCreated (Cmp{}) = [0]
varsCreated (Call{}) = []
varsCreated (Dealloc{}) = undefined
varsCreated _  = [1]

-- vals referenced in a cont
-- does not do recursively
-- NOTE: breaks when dealloc is involved
valsUsed :: Cont -> [Val]
valsUsed (Io _ vs _ _) = vs
valsUsed (Cmp _ va vb _ _) = [va,vb]
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

closureConvert :: Code -> Code
closureConvert c = c { codeFns = f $ runState st (length fns, []) } where
  fns :: [CodeFn]
  fns = codeFns c
  f :: ([a], (t, [a])) -> [a]
  f (x, (_, y)) = x <> y
  st :: State (Int, [CodeFn]) [CodeFn]
  st = foldr (\v l -> (:) <$> convertIndividual v <*> l) (pure []) fns
  convertIndividual :: CodeFn -> State (Int, [CodeFn]) CodeFn
  convertIndividual (a, c) = (a,) <$> closureConvert' appendFn c
  appendFn :: a -> State (Int, [a]) Int
  appendFn f = do
    (n, fs) <- get
    put (n+1, f:fs)
    pure n


main = pure ()
