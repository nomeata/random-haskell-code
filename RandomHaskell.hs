{-# LANGUAGE StandaloneDeriving, RankNTypes, ScopedTypeVariables #-}

import Language.Haskell.Exts          -- haskell-src-exts
import Data.Generics.Uniplate.Data    -- uniplate
import Data.List
import Data.Data
import System.Environment
import Control.Monad.Random
import qualified Data.Map.Strict as M
import Data.Functor
import Control.Monad
import Data.Maybe
import Unsafe.Coerce
import System.IO

deriving instance Ord ConstrRep

data MyCon = MyCon ConstrRep | Str String deriving (Eq, Ord)

type Key = (TypeRep, ShortCtxt)
type ConOccs = [(Key, MyCon)]
type ConMap = M.Map MyCon Int
type TyMap a = M.Map Key a

type Ctxt = [(TypeRep, MyCon, Int)]
type ShortCtxt = Ctxt

-- This is an interesting knob to turn. Larger means more realistic code, but
-- also more memory requirement and more code that should be read
shortenCtxt :: Ctxt -> ShortCtxt
shortenCtxt = take 3

extendCtxt :: Data a => a -> MyCon -> Int -> Ctxt -> Ctxt
-- Ignore one-constructor, one field data types
extendCtxt x (MyCon c) i ctxt
    | AlgRep [c'] <- dataTypeRep (dataTypeOf x)
    , [_] <- constrFields c'
    = ctxt
extendCtxt x mc i ctxt = (typeOf x,mc,i) : ctxt

genListLength :: Data a => a -> Maybe Int
genListLength x = do
  let t = typeOf x
  (tc,[a]) <- return $ splitTyConApp t
  guard (tc == fst (splitTyConApp (typeOf "hi")))
  let l = unsafeCoerce x :: [()]
  return (length l)


getConOccs :: Data a => Ctxt -> a -> ConOccs
getConOccs ctxt x 
    | Just s <- cast x
    = [ (key, Str s) ]
    | otherwise
    = let mc = MyCon (constrRep (toConstr x))
          ctxt' i = extendCtxt x mc i ctxt
      in (key, mc) : 
         concat (zipWith (\f i -> (f i))
                    (gmapQ (\y i -> getConOccs (ctxt' i) y) x)
                    [0..])
  where
    key = (t, shortenCtxt ctxt)
    t = typeOf x

singletonConMap :: MyCon -> ConMap
singletonConMap c = M.singleton c 1

conMapAdd :: ConMap -> ConMap -> ConMap
conMapAdd = M.unionWith (+)

toTypeMap :: ConOccs -> TyMap ConMap
toTypeMap = foldl (\m (t,c) -> M.insertWith conMapAdd t (singletonConMap c) m) M.empty

selectRandom :: Double -> M.Map r Int -> r
selectRandom r m = go i (M.toList m)
  where
  go i ((x, n):rs) = if i < n then x else go (i-n) rs
  go i [] = error "miscalculation"
  total = sum (M.elems m)
  i = floor (r * fromIntegral total)

randData :: forall a. Data a => TyMap ConMap -> Ctxt ->  Rand StdGen a
randData tm ctxt = do
    r <- getRandom 
    let mc = selectRandom r cm
        ctxt' i = extendCtxt x mc i ctxt
    case mc of 
        MyCon c -> fromConstrMI (\i -> randData tm (ctxt' i)) (repConstr (dataTypeOf x) c)
        Str s -> return $ fromJust $ cast s
  where
    t = typeOf x
    cm = tm M.! (t, shortenCtxt ctxt)
    x = undefined :: a
    
parseMode = defaultParseMode { fixities = Nothing }

main = do
    args <- getArgs
    modsParses <- mapM (parseFileWithMode parseMode) args
    sequence_ [ hPutStrLn stderr $ prettyPrint l ++ ": " ++ e | ParseFailed l e <- modsParses]

    let mods = [m | ParseOk m <- modsParses]

    let cons = toTypeMap $ concatMap (getConOccs []) mods

    m <- evalRandIO (randData cons []) :: IO Module

    putStrLn (prettyPrint m)

data PairM m x = PM Int (m x)
unPairM (PM x m) = m

fromConstrMI :: forall m a. (Monad m, Data a)
            => (forall d. Data d => Int -> m d)
            -> Constr
            -> m a
fromConstrMI f con = unPairM (gunfold k z con)
 where
  k :: forall b r. Data b => PairM m (b -> r) -> PairM m r
  k (PM i c) = PM (i+1) (do { c' <- c ; b <- f i; return (c' b) })

  z :: forall r. r -> PairM m r
  z x = PM 0 (return x)

