{-# LANGUAGE PackageImports, GADTs, KindSignatures, StandaloneDeriving, EmptyDataDecls, FlexibleInstances, OverloadedStrings #-}

module Display (Pretty(..), Doc, ($$), (<+>), text, hang, vcat, parensIf, sep, comma, nest, parens,
                subscriptPretty, superscriptPretty, subscriptShow, punctuate, render, module Data.Monoid, (Display.<>)) where

import GHC.Exts( IsString(..) )

import Prelude hiding (length, reverse)
import Text.PrettyPrint.HughesPJ hiding ((<>))
import qualified Text.PrettyPrint.HughesPJ 
import Numeric (showIntAtBase)
import Control.Arrow (second)
import Control.Monad.Error
import Data.Monoid hiding ((<>))
import Data.Sequence hiding (empty)
import Data.Foldable

(<>) :: Monoid a => a -> a -> a
(<>) = mappend

class Pretty a where
    pretty :: a -> Doc

instance Pretty x => Pretty [x] where
    pretty x = brackets $ sep $ punctuate comma (map pretty x)

instance (Pretty a,Pretty b) => Pretty (a,b) where
    pretty (a,b) = parens $ pretty a Display.<> comma <+> pretty b 

instance Pretty Int where
  pretty = int

instance Pretty Bool where
  pretty = text . show

scriptPretty :: String -> Int -> Doc
scriptPretty s = text . scriptShow s

scriptShow (minus:digits) x = if  x < 0 then minus : sho (negate x) else sho x
  where sho x = showIntAtBase 10 (\i -> digits !! i) x []

superscriptPretty = scriptPretty "⁻⁰¹²³⁴⁵⁶⁷⁸⁹"
subscriptPretty   = scriptPretty "-₀₁₂₃₄₅₆₇₈₉"

subscriptShow :: Int -> String
subscriptShow     = scriptShow "-₀₁₂₃₄₅₆₇₈₉"

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id


