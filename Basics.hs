{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}
module Basics
       (module Data.Monoid, (<>),
        module Control.Applicative,
        Irr(..), 
        Sort(..),
        Ident, Identifier(..), DisplayContext,
        Position, dummyPosition, identPosition, 
        isDummyId, modId, synthId, dummyId, idString,
        Binder(..), arrow, colon, cross, appl, comm,
        Lattice(..), above,
        module Cubes) where

import Display
import qualified RawSyntax as A
import RawSyntax (Identifier(..))
import Control.Applicative
import Data.Monoid
import Data.Sequence (Seq)
import Cubes

-----------
-- Irr

newtype Irr a = Irr {fromIrr :: a}
    deriving (Show,Monoid)

instance Eq (Irr a) where
    x == y = True

instance Pretty x => Pretty (Irr x) where
    pretty (Irr x) = pretty x

--------------
-- Ident
instance Pretty Identifier where
    pretty (Identifier (_,x)) = text x

instance Monoid Identifier where
  Identifier (p,t1) `mappend` Identifier (_,t2) = Identifier (p, t1 <> t2)
  mempty = Identifier (fromIrr dummyPosition,"")

type Ident = Irr Identifier

isDummyIdS ('_':x) = True
isDummyIdS _ = False

isDummyId (Irr (Identifier (_,xs))) = isDummyIdS xs

synthId :: String -> Ident
synthId x = Irr (Identifier (fromIrr dummyPosition,x))

dummyId = synthId "_"

idString :: Ident -> String
idString (Irr (Identifier (_,name))) = name

type DisplayContext = Seq Ident

----------------
-- Position

type Position = (Int,Int)

identPosition (Irr (Identifier (p,_))) = Irr p

dummyPosition = Irr (0,0)

modId :: (String -> String) -> Ident -> Ident
modId f (Irr (Identifier (pos ,x)))  = (Irr (Identifier (pos,f x)))

-------
-----------
-- Sort


instance Lattice Int where -- Lattice is a misnomer here.
    x ⊔ (-1) = (-1)
    x ⊔ y = max x y

data Binder = Pred | Regu
  deriving (Ord,Eq,Show)
                      
class Lattice a where
    (⊔) :: a -> a -> a

-- instance Ord Sort where
--  compare (Sort x) (Sort y) = compare x y

data Sort = Sort {sortLevel :: Int,
                  sortDimension :: Int}
  deriving (Eq)

instance Lattice Sort where
  Sort x m ⊔ Sort y n  = Sort (x ⊔ y) (min m n)
  

instance Show Sort where
    show s = render (pretty s)


instance Pretty Binder where
    pretty = colon

instance Pretty Sort where
    pretty (Sort s d) = showLev <> showDim

     where showDim = case d of
                       0 -> mempty
                       _ -> superscriptPretty d
           showLev = case s of
                       (-1) -> "□"
                       0    -> star
                       l    -> star <> subscriptPretty l
                       

above (Sort s n) = Sort (s+1) n    

star = "∗" -- ⋆★*∗


arrow, colon, cross, comm, appl :: Binder -> Doc

arrow Pred = "⇛"
arrow Regu = "→"
-- ⟴

colon Regu = text ":"
colon Pred = text "::"
-- :⋮∷∴∵


cross Regu = "×" 
cross Pred  = "⋇" 
-- ⊗⊠
-- ⚔⤬⤫⨯

comm Pred = "⍮"
comm Regu = ","


appl Regu = "" 
appl Pred = "· " 

