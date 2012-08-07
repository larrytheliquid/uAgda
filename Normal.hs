{-# LANGUAGE GADTs, KindSignatures, OverloadedStrings, EmptyDataDecls, StandaloneDeriving, TypeSynonymInstances, TypeFamilies, MultiParamTypeClasses, ViewPatterns, RankNTypes #-}
module Normal where

import Prelude hiding (length,elem,foldl)
import Basics
import Display
import Data.Foldable
import Control.Arrow (first, second)
import Data.Sequence hiding (zip,replicate,reverse)
import Options
import qualified Data.List as L
import Permutation

data No
data Ne
data Va

type NF = Term No
type Neutral = Term Ne
type Variable = Term Va
type NF' = (NF, NF) -- value, type.

data Role = Index | Thing deriving (Eq, Show)

showRole Index = "?"
showRole Thing = "!"

data Term n :: * where
     Neu :: Neutral -> NF
     Var :: Variable -> Neutral
     
     Star :: Sort -> NF     
     
     Pi  :: Binder -> Ident -> Cube NF -> NF -> NF
     Lam :: Binder -> Ident -> Cube NF -> NF -> NF 
     App :: Binder -> Neutral -> Cube NF -> Neutral -- The sort is that of the argument.
     
     Sigma :: Binder -> Ident -> NF -> NF -> NF
     Pair  :: Binder -> Ident -> NF -> NF -> NF  -- Pair does not bind any variable.
     Proj  :: Binder -> -- ^ Sort of the argument (only needed for
                           -- the 1st projection: 2nd projection does
                           -- not change relevance)
              Neutral -> Bool -> -- ^ True for 1st projection; False for 2nd.
              Ident -> Neutral 
     
     
     -- OfParam :: Ident -> NF -> Neutral

     -- Destr :: Int -> Variable -> Variable -- argument: depth where destruction occurs.
     Swap :: Permutation -> Variable -> Variable
     Param :: Role {-TODO: Maybe the swap should be merged into the role -} -> Variable -> Variable 
     V :: BitVector -> Int -> Variable -- shift, deBruijn 
     Hole :: Irr String -> Variable

type Subst = [Cube NF]

deriving instance Eq (Term n)
deriving instance Show (Term n)

var :: Int -> NF
var x = Neu $ var' x

var'' = V nil

var' x = Var $ V nil x


-- | Hereditary substitution
subst0 :: Cube NF -> NF -> NF
subst0 u = subst (u:map (unit . var) [0..])  

hole = Neu . Var . Hole . Irr

subst :: Subst -> Term n -> NF
subst f t = case t of
  Neu x -> s x
  Var x -> s x
  
  Star x -> Star x
  
  Lam o i ty bo -> Lam o i (fmap s ty) (s' bo)
  (Pair o i x y) -> Pair o i (s x) (s y)
  Pi o i a b -> Pi o i (fmap s a) (s' b)
  Sigma o i a b -> Sigma o i (s a) (s' b)
  (App o a b) -> app o (s a) (fmap s b)
  (Proj o x k f) -> proj o (s x) k f

--  OfParam i x -> Neu (OfParam i (s x))
  
--  Destr d x -> destroy d (s x)
  Hole (Irr x) -> hole x
  V bv x -> let fx = f!!x in
            case cubeElems fx of 
              [Neu (Var (V bv' y))] -> Neu $ Var $ V (bv' <> bv) y
              _ | dim (f !! x) /= bvDim bv -> hole $ "error: variable access dim " ++ show (bvDim bv) ++ " expected " ++ show (dim (f!!x))
              _  -> (f !! x) !? bv 
  Param r x -> param r (s x)
  Swap q x -> swap q (s x)
 where s,s' :: forall n. Term n -> NF
       s' = subst (unit (var 0) : map (cmap wk) f)
       s  = subst f

both f (x,y) = (f x, f y)

-----------------------------
-- Hereditary operations

app :: Binder -> NF -> Cube NF -> NF 
app Pred x u | dim u == 0 = x
app _ (Lam _ i _ bo) u = subst0 u bo
app o (Neu n)      u = Neu (App o n u)

-- TODO: merge App Pred's

proj :: Binder -> NF -> Bool -> Ident -> NF
proj _ (Pair _ _ x y) True f = x
proj _ (Pair _ _ x y) False f = y
proj o (Neu x) k f = Neu (Proj o x k f)


wkn :: Int -> NF -> NF
wkn = wkdn 0

wkdn :: Int -> Int -> NF -> NF
wkdn d n = subst (map (unit . var) [0..d-1] ++ map (unit . var) [d+n..])

wk = wkn 1
str = strn 1
strn n = subst (replicate n (unit $ hole "str: oops!") ++ map (unit . var) [0..])

wkv :: Int -> Variable -> Variable
wkv n (Param r x) = Param r (wkv n x)
wkv n (Swap q x) = Swap q (wkv n x)
wkv n (V s x) = V s (x + n)
wkv n (Hole x) = Hole x


param :: Role -> NF -> NF
param r = transNF r noAction


-----------------------------------
-- Display

dec xs = [ x - 1 | x <- xs, x > 0]

allFreeVars :: Cube (Term n) -> [Int]
allFreeVars = L.concat . fmap freeVars . cubeElems

freeVars :: Term n -> [Int]
freeVars (Var x) = freeVars x
--freeVars (Destr _ x) = freeVars x
freeVars (Neu x) = freeVars x
freeVars (Pi _ _ a b) = allFreeVars a <> (dec $ freeVars b)
freeVars (Sigma _ _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (V _ x) = [x]
freeVars (App _ a b) = freeVars a <> allFreeVars b
freeVars (Lam _ _ ty b) = allFreeVars ty <> (dec $ freeVars b)
freeVars (Star _) = mempty
freeVars (Hole _) = mempty
freeVars (Pair _ _ x y) = freeVars x <> freeVars y
freeVars (Proj _ x _ _) = freeVars x
freeVars (Param _ x) = freeVars x
freeVars (Swap _ x) = freeVars x
-- freeVars (OfParam _ x) = freeVars x

iOccursIn :: Int -> Term n -> Bool
iOccursIn x t = x `elem` (freeVars t)

allocName :: DisplayContext -> Ident -> Ident
allocName g s 
  | fromIrr s `elem` (fmap fromIrr g) = allocName g (modId (++ "'") s)
  | otherwise = s

printIndex :: DisplayContext -> Int -> Doc
printIndex ii k 
  | k < 0 || k >= length ii  = text "<deBrujn index" <+> pretty k <+> text "out of range>"
  | otherwise = pretty (ii `index` k)

cPrint :: Int -> DisplayContext -> Term n -> Doc
cPrint p ii (Swap q x) = cPrint p ii x <> "#" <> pretty q
cPrint p ii (Var x) = cPrint p ii x
cPrint p ii (Neu x) = cPrint p ii x
cPrint p ii (Param r x) = cPrint p ii x <> text (showRole r)
-- cPrint p ii (Destr d x) = cPrint p ii x <> "%" <> pretty d
-- cPrint p ii (OfParam i x) = pretty i
                             -- "⌊" <> cPrint (-1) ii x <> "⌋"
cPrint p ii (Hole (Irr x)) = text x
cPrint p ii (Star i) = pretty i
cPrint p ii (V bv k) = printIndex ii k <> (mconcat $ map subscriptPretty $ map b2i $ bits bv)
cPrint p ii (Proj o x k (Irr f))     = cPrint p ii x <> (if k then "." <> pretty f else "/")
cPrint p ii t@(App _ _ _)     = parensIf (p > 3) (cPrint 3 ii fct <+> sep [appl o <> printCube o 4 ii a | (o,a) <- args]) 
    where (fct,args) = nestedApp t
cPrint p ii t@(Pi _ _ _ _)    = parensIf (p > 1) (printBinders arrow ii mempty $ nestedPis t)
cPrint p ii t@(Sigma _ _ _ _) = parensIf (p > 1) (printBinders cross ii mempty $ nestedSigmas t)
cPrint p ii (t@(Lam _ _ _ _)) = parensIf (p > 1) (nestedLams ii mempty t)
cPrint p ii (Pair o name x y) = parensIf (p > (-1)) (sep [pretty name <+> text "=" <+> cPrint 0 ii x <> comm o,
                                                          cPrint (-1) ii y])

nestedPis  :: NF -> ([(Ident,Bool,Cube NF,Binder)], NF)
nestedPis (Pi o i a b) = (first ([(i,0 `iOccursIn` b,a,o)] ++)) (nestedPis b)
nestedPis x = ([],x)

nestedSigmas  :: NF -> ([(Ident,Bool,Cube NF,Binder)], NF)
nestedSigmas (Sigma o i a b) = (first ([(i,0 `iOccursIn` b,unit a,o)] ++)) (nestedSigmas b)
nestedSigmas x = ([],x)

printBinders :: (Binder -> Doc) -> DisplayContext -> Seq Doc -> ([(Ident,Bool,Cube NF,Binder)], NF) -> Doc
printBinders sep ii xs (((x,occurs,a,o):pis),b) = printBinders sep (i <| ii) (xs |> (printBind' ii i occurs a o <+> sep o)) (pis,b)
        where i = allocName ii x
printBinders _ ii xs ([],b)                 = sep $ toList $ (xs |> cPrint 1 ii b) 


nestedLams :: DisplayContext -> Seq Doc -> Term n -> Doc
nestedLams ii xs (Lam o x ty c) = nestedLams (i <| ii) (xs |> parens (pretty i <+> colon o <+> printCube o 0 ii ty)) c
                                  where i = allocName ii x
nestedLams ii xs t         = (text "\\ " <> (sep $ toList $ (xs |> "->")) <+> nest 3 (cPrint 0 ii t))

printCube :: Binder -> Int -> DisplayContext -> Cube (Term n) -> Doc
printCube o p ii d | dim d == 0 = cPrint p ii (d !? nil)
                   | otherwise = "{" <> sep (punctuate ";" [(if showIndices options then pretty i <> "↦" else mempty ) <>
                                                            cPrint 0 ii x | (i,x) <- adjust $ cubeAssocs d]) <> "}"
 where adjust = case o of
                  Pred -> init
                  Regu -> id

printBind' ii name occurs d o = case not (isDummyId name) || occurs of
                  True -> parens $ pretty name <+> colon o <+> printCube o 0 ii d
                  False -> printCube o 2 ii d
                  
nestedApp :: Neutral -> (Neutral,[(Binder, Cube NF)])
nestedApp (App o f a) = (second (++ [(o,a)])) (nestedApp f)
nestedApp t = (t,[])

prettyTerm = cPrint (-100)


instance Pretty (Term n) where
    pretty = prettyTerm mempty

type Action = [(NF,NF)] -- TODO: use Seq

paramv :: BitVector -> Role -> Int -> NF
paramv bv Thing x = Neu $ Var $ Param Thing $ V bv x
paramv bv Index x = Neu $ Var $               V bv x

noAction = []
wka = map (both wk)
addAct1 as = (Neu $ Var $ V (zeros 1) 0, Neu $ Var $ V (ones 1) 0) : wka as
addAct2 as = error "accessing crap" : wka as


recVarName = synthId "°"

scopeCheck c k | 0 `iOccursIn` c = error "swapTy: improperly scoped Sigma"
               | otherwise = c

swap q = swapNF q 0

swapV :: Permutation  -> Variable -> Variable
swapV q x | isIdentity q = x
swapV q (V bv x) = Swap q $ V bv x

swapV q (Swap q' v) = swapV (q `after` q') v 
swapV q v@(Param _ _) | isIdentity q' = v
                      | otherwise = Swap (simplifyPerm n q) v
    where n = countParam v
          q' = simplifyPerm n q
swapV q (Hole (Irr s)) = Hole $ Irr (s ++ "#")
swapV q x = Swap q x

-- FIXME: what about the role=Index? There should not be a (Param Index) in the syntax.
countParam (Param Thing x) = 1 + countParam x
countParam x = 0

fullVarCube x = full (\i -> Neu $ Var $ V i x) 

swapSubst :: Permutation -> NF -> NF
swapSubst q = subst $ (apply (invert q) $ fullVarCube 0 $ permLength q) : map (unit . var) [1..]

swapNe :: Permutation -> Int -> Neutral -> Neutral
swapNe q d (Var v) = Var $ swapV q v
swapNe q d (App o f a) = App o (swapNe q d f) (swapCube q d a)
swapNe q d (Proj o x k f) = Proj o (swapNe q d x) k f 

swapCube :: Permutation -> Int -> Cube NF -> Cube NF
swapCube q0 d c = apply q . subAppl q (\p -> swapNF p d) $ c
  where q = reducePerm q0 (dim c) -- FIXME: reduction should never be
                                  -- necessary; we have dimension
                                  -- checks.

swapBinder :: Permutation -> Int -> Cube NF -> Cube NF
swapBinder = swapCube

swapNF :: Permutation -> Int -> NF -> NF
swapNF q d (Neu v) = Neu $ swapNe q d v
swapNF q d (Star x) = Star x
-- swapNF q d (Pair  o i a b) = Pair  o i (swapBinder q d a) (swapNF q d b)
swapNF q d (Lam   o i a b) = Lam   o i (swapBinder q d a) (swapSubst q $ swapNF q (d+1) b)
swapNF q d (Pi    o i a b) = Pi    o i (swapBinder q d a) (swapSubst q $ swapNF q (d+1) b)
-- swapNF q d (Sigma o i a b) = Sigma o i (swapBinder q d a) (swapNF q (d+1) b)

getVar :: Variable -> Int
getVar (Param _ x) = getVar x
getVar (V _ x) = x
getVar (Hole x) = (-1)
getVar (Swap _ x) = getVar x

getDepth :: Variable -> Int
getDepth (Param _ x) = 1 + getDepth x
getDepth (V _ x) = 0
getDepth (Hole x) = 0
getDepth (Swap _ x) = getDepth x


-- | Transform a term to its relational interpretation
transV :: Role -> Action -> Variable -> NF
transV Thing d (Swap q x) = swap (extendPerm q) $ transV Thing d x
transV Index d (Swap q x) = swap q $ transV Index d x
transV r d (V bv x) | x < L.length d = Neu $ Var $ case r of Thing -> V (bv <> ones 1) x; Index -> V (bv <> zeros 1) x
                    | otherwise = paramv bv r x
-- transV r [] (Param r' x) = Neu $ Var $ Param r $ Param r' x 
transV r d  (Param r' x) 
            | getVar x < L.length d = maybeSwap $ param r' $ transV r d x -- the inner variable is known; go through 
            | otherwise = Neu $ Var $ maybeParam $ Param r' x -- the inner variable is not known ~> stop here and forget about other variables
              where maybeSwap = if r == Thing then swap (swap2 (n+2) (n+1) n) else id -- add a swap if we are doing "proper" parametricity
                    maybeParam = if r == Thing then Param r else id -- keep only "proper" parametricity
                    n = getDepth x

transV r d  (Hole (Irr s)) = hole (s ++ showRole r)

transNe :: Role -> Action -> Neutral -> NF
transNe r d (Var v)      = transV r d v
transNe Thing d (App o f a)  = app o (transNe Thing d f) (extend d a)
transNe Index d (App o f a)  = app o (transNe Index d f) (cmap (transNF Index d) a)
transNe r d (Proj o x k f) = proj o (transNe r d x) k f

isLam :: Term n -> Bool
isLam (Lam _ _ _ _) = True
isLam _ = False

transNF :: Role -> Action -> NF -> NF
transNF r d (Neu v) = transNe r d v
transNF r d p@(Lam Pred i ty bo) = Lam Pred i (updateCube ix p $ extend d ty) (inTrans (addAct1 d) bo (Neu $ Var $ V ix 0))
    where ix = ones (dim ty) <> zeros 1
transNF r d (Lam o i ty bo)    = Lam o i (extend d ty) (transNF r (addAct1 d) bo)
transNF r d (Pair o i x y)     = Pair o i (transNF r d x) (transNF r d y) 
transNF Index d (Star x)       = Star x
transNF Index d (Pi o i a b)    = Pi    o i (cmap (transNF Index d) a) (transNF Index d b)
transNF Index d (Sigma o i a b) = Sigma o i ((transNF Index d) a) (transNF Index d b)
transNF r d ty@(Star  _)       = trans' r d ty
transNF r d ty@(Pi    _ _ _ _) = trans' r d ty
transNF r d ty@(Sigma _ _ _ _) = trans' r d ty

extend  d a  = cubeCons (cmap (transNF Index d) a) (cmap (transNF Thing d) a) 

trans' :: Role -> Action -> NF -> NF
trans' Index d ty = error $ "trans': Index: wrong arg: " ++ show ty
trans' Thing d ty = Lam Pred (synthId "z") (unit1 (transNF Index d ty)) (zerInRel d ty)

-- | Build the relation x ∈ ⟦ty⟧. (where 'x' is 0; but not bound in 'ty'.)
zerInRel :: Action -> NF -> NF
zerInRel d ty = inTrans (addAct2 d) (wk ty) (Neu $ Var $ V (zeros 1) 0)

-- | Build a relation z ∈ ⟦ty⟧.  z is a term that, after renaming,
-- gives the vector of terms member of the relation.  Note that
-- 'trans' is never applied to 'z', therefore 'zR' never occurs in the result.


inTrans :: Action -> NF -> NF -> NF
inTrans d (Neu (App Pred f a))  z = app Pred (transNe Thing d f) (updateCube (ones (dim a) <> zeros 1) z (extend d a))
inTrans d (Star (Sort l δ))       z = (Pi Pred dummyId (unit1 z) (Star $ Sort l (δ+1)))
inTrans d (Pi    Pred i a (Star (Sort l δ))) z = Pi Pred i (updateCube (ones (dim a) <> zeros 1) z (extend d a)) (Star $ Sort l (δ+1))
inTrans d (Pi    o i a b) z = Pi o i (extend d a) (inTrans (addAct1 d) b (app o (wk z) (unit $ transNF Index (addAct1 d) $ var 0)))
inTrans d (Sigma o i a b) z = Sigma o i (inTrans d a (proj o z True i))
                                        (inTrans ((wk $ proj o z True i,var 0):wka d) b (proj o (wk z) False i))
inTrans d ty z = app Pred (transNF Thing d ty) (unit1 z)

unit1 z = (pair z (hole "⊘"))