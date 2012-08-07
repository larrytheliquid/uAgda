{-# LANGUAGE TypeSynonymInstances #-}

module Cubes where

import Data.List 
import Data.Array.IArray
import Data.Char
import Display
import Data.Monoid
import Permutation

data Bit = Zero | One deriving (Ord,Eq,Ix)

newtype BitVector = BV { unBV :: Array Int Bit} deriving (Eq)

instance Ord BitVector where
   (BV i) <= (BV j) = all (\d -> i!d <= j!d) (range $ bounds i)
   i < j = i <= j && i /= j 

type Cube a = Array BitVector a

bitsFromString :: String -> [Bit]
bitsFromString ('0':xs) = Zero : bitsFromString xs
bitsFromString ('1':xs) = One  : bitsFromString xs
bitsFromString [] = []

bvFromString :: String -> BitVector
bvFromString s = BV $ listArray (dims $ length s) (bitsFromString s)

subscriptPrettyBV :: BitVector -> Doc
subscriptPrettyBV bv = mconcat $ map (subscriptPretty . b2i) $ elems $ unBV $ bv

instance Monoid BitVector where
    mempty = nil
    mappend i j = BV $ listArray (dims $ bvDim i + bvDim j) $ elems (unBV i) ++ elems (unBV j)

cubeAccess :: String -> Cube a -> BitVector -> a
cubeAccess loc c i | dim c /= bvDim i = error $ loc ++ ": cube access: mismatched dimensions: " ++ show (dim c) ++ " /= " ++ show (bvDim i)
       | otherwise = c ! i

(!?) :: Cube a -> BitVector -> a
c !? i = cubeAccess "??" c i

instance Show Bit where
    show Zero = "0"
    show One = "1"

instance Show BitVector where
    show  = concatMap show . elems . unBV

b2i Zero = 0
b2i One  = 1

cubeElems :: Cube a -> [a]
cubeElems = elems

cubeAssocs :: Cube a -> [(BitVector,a)]
cubeAssocs = assocs

bits :: BitVector -> [Bit]
bits = elems . unBV

bitsToInt :: [Bit] -> Int
bitsToInt [] = 0
bitsToInt (x:xs) = b2i x + 2 * (bitsToInt xs)

toInt :: BitVector -> Int
toInt = bitsToInt . reverse . elems . unBV

-- | Number of set bits in the vector
setBits :: BitVector -> Int
setBits (BV i) = sum $ map b2i $ elems $ i

-- | Number of set clear in the vector
clearBits i = bvDim i - setBits i

bvTail (BV i) = BV $ listArray (0,h-1) $ tail $ elems i
  where (0,h) = bounds i

bvIndex :: BitVector -> Int
bvIndex i | i == nil = 1
bvIndex i | otherwise = case unBV i!0 of
                  Zero -> bvIndex (bvTail i) 
                  One  -> bvIndex (bvTail i) + choose (bvDim i-1) (setBits i) 

choose n 0 = 1
choose 0 k = 0
choose n k = choose (n-1) (k-1) * n `div` k

prettyBV0 :: BitVector -> String
prettyBV0 i = chr (ord 'a' + setBits i) : show (bvIndex i)

instance Pretty BitVector where
    pretty = text . show

specialPretty i = superscriptPretty (setBits i) <> subscriptPretty (bvIndex i)

instance Ix BitVector where
    index (l,h) i = toInt i - toInt l
    range (BV l,BV h) = [BV $ listArray (bounds l) i | i <- rngs (elems l) (elems h)]
    inRange (BV l,BV h) (BV i) = all (\(d,j) -> inRange (l!d,h!d) j) (assocs i) 

-- "Product" of ranges
rngs [] [] = [[]]
rngs (a:as) (b:bs) = [x:xs | x <- range (a,b), xs <- rngs as bs]


bvDim i = 1 + (snd $ bounds $ unBV i)

-- Dimension of a cube
dim :: Cube a -> Int
dim c = bvDim (snd $ bounds $ c)

-- "Range" for a bitvector of dim. d
dims  d = (0,d-1)

zeros d = BV $ listArray (dims d) (replicate d Zero)
ones  d = BV $ listArray (dims d) (replicate d One)
nil :: BitVector
nil     = BV $ listArray (dims 0) [] 

-- "Range" for a cube
spn  d = (zeros d, ones d)

instance Permutable BitVector where
  apply p (BV i) = BV $ ixmap (bounds i) (apply p) i

-- instance Permutable (Cube a) where
--   apply p c = ixmap (bounds c) (apply p) c

instance (Ix ix,Permutable ix) => Permutable (Array ix a) where
    apply p a = ixmap (bounds a) (apply p) a

b2b Zero = False
b2b One  = True

bv2bools (BV bv) = map b2b $ elems bv

-- Apply a function on elements of the cube that lie at the intersection of 2 dimensions
subAppl :: Permutation -> (Permutation -> a -> a) -> Cube a -> Cube a
subAppl p f c = listArray (bounds c) [f (project p (bv2bools i)) e | (i,e) <- assocs c]


full :: (BitVector -> a) -> Int -> Cube a
full f d = array (spn d) [(i,f i) | i <- range $ spn d]

unit :: a -> Cube a
unit a = listArray (spn 0) [a]

pair :: a -> a -> Cube a
pair a b = listArray (spn 1) [a,b]

cmap :: (a -> b) -> Cube a -> Cube b
cmap = fmap

{-
prettyCube :: Cube Doc -> [Doc]
prettyCube terms = [a ++ " " ++ prettyArgs i terms | (i,a) <- assocs terms]
-}

projectDim d valueKept c
    | d0 == 0 = error "projecting trivial cube"
    | d >= d0 = error "projecting away non-existing dimension"
    | otherwise = listArray (spn $ d0-1) [a | (i,a) <- assocs c, unBV i!d == valueKept]   
    where d0 = dim c

-- prettyArgs :: BitVector -> Cube Doc -> Doc
-- prettyArgs i c = foldr mempty (<+>) [a | (j,a) <- assocs c, j < i] 


interleave [] [] = []
interleave (x:xs) (y:ys) = x:y:interleave xs ys

cubeCons :: Cube a -> Cube a -> Cube a
cubeCons c1 c2 = listArray (spn (d+1)) (interleave (elems c1) (elems c2))
 where d = dim c1


subCubeAt :: BitVector -> Cube a -> Cube a
subCubeAt i c = listArray (spn d) [a | (j,a) <- assocs c, keep j]
  where d0 = dim c
        d = d0 - clearBits i
        keep j = and [(x == One) || (y == Zero) | (x,y) <- zip (elems $ unBV i) (elems $ unBV j)]

updateCube :: BitVector -> a -> Cube a -> Cube a
updateCube i x c = c // [(i,x)]

log2 :: Int -> Maybe Int
log2 0 = Nothing
log2 1 = return 0
log2 x = case quotRem x 2 of
           (x',0) -> (+1) `fmap` log2 x'
           (_,1) -> Nothing
  

cubeFromList :: [a] -> Maybe (Cube a)
cubeFromList xs = do
  dim <- log2 (length xs)
  return $ listArray (spn dim) xs

