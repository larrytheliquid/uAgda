module Permutation where

import Data.Char
import Display
import Data.Monoid
import Data.List
import Data.Maybe
import Data.Tree (flatten)
import Data.Graph (dff, Graph)
import Data.Array

type Orbit = [Int]
type Orbits = [Orbit]

mkPerm :: [Int] -> Permutation
mkPerm xs | sort xs == [0..length xs-1] = P xs
          | otherwise = error $ "malformed permutation: " ++ show xs

liftPermut (P xs) = P (xs ++ [length xs])

permFromString "" = P [1,0]
permFromString xs = mkPerm . map digitToInt $ xs

newtype Permutation = P {unP :: [Int]} deriving (Eq)

instance Show Permutation where
    show = show . orbitsFromPerm 

permLength = length . unP

invert :: Permutation -> Permutation
invert (P xs) = P [fromJust $ elemIndex x xs | x <- [0..length xs-1]]

project :: Permutation -> [Bool] -> Permutation
project (P perm) proj = P (map toIndex $ sort projected)
  where projected = [x | (x,bit) <- zip perm proj, bit]
        toIndex x = fromJust $ elemIndex x projected
  
instance Permutable Int where
  apply (P p) i = p !! i

swap2 :: Int -> Int -> Int -> Permutation 
swap2 n i j 
  | i >= n || j >= n = error $ "swap2: wrong arguments: " ++ show (n,i,j)
  | otherwise = mkPerm $ map f [0..n-1]
  where f x | x == i = j
            | x == j = i
            | otherwise = x

after :: Permutation -> Permutation -> Permutation
(P p) `after` (P q) = P $ [p!!(q!!i) | i <- [0..length q-1]]

      

class Permutable a where
    apply :: Permutation -> a -> a

instance Pretty Permutation where
  pretty (P [1,0]) = mempty
  pretty (P xs) = mconcat $ map pretty $ xs


isIdentity (P x) = x == [0..length x-1]


extendPerm (P x) = P $ x ++ [length x]

reducePerm (P x) n | n == length x = P x
                   | n > length x = error "reduction attempted when extension should have been done"
                   | r /= [n .. length x - 1] = error $ "permutation " ++ show x ++ " cannot be reduced to dimension " ++ show n
                   | otherwise = P l
  where (l,r) = splitAt n x


simplifyPerm :: Int -> Permutation -> Permutation
simplifyPerm n xs = permFromOrbits (length . unP $ xs) . filter usefulOrbit . orbitsFromPerm $ xs
  where usefulOrbit :: Orbit -> Bool
        usefulOrbit = or . map (>= n)

permAsGraph :: Permutation -> Graph
permAsGraph (P xs) = listArray (0,length xs-1) $ map (:[]) xs


-- | Returns the orbits of a permutation, as a partition
orbitsFromPerm :: Permutation -> Orbits
orbitsFromPerm = map flatten . dff . permAsGraph

-- | Returns a permutation whose orbits are given.
permFromOrbits :: Int -> Orbits -> Permutation
permFromOrbits dimension orbits = P $ elems $ accumArray (\_ x-> x) 0 bnds (base ++ cycles)
          
    where cycleOf' first (v1:v2:vs) = (v1, v2) : cycleOf' first (v2:vs)
          cycleOf' first (v:[]) = [(v, first)]
          cycleOf' _ _ = []
          cycleOf orbit@(v:_) = cycleOf' v orbit
          cycleOf _ = []
          bnds = (0,dimension-1)
          base = [(i,i) | i <- range bnds]
          cycles = concat $ map cycleOf $ orbits