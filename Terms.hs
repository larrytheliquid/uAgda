{-# LANGUAGE PackageImports, GADTs, KindSignatures, StandaloneDeriving, EmptyDataDecls, FlexibleInstances, OverloadedStrings #-}

module Terms(Ident, Irr(..), Identifier(..), Sort(..), 
             Term(..), 
--                 bound, app, proj, 
                      prettyTerm,
             Position, dummyPosition, identPosition, termPosition,
             isDummyId, synthId, dummyId, 
--             destruction,
            -- wk, wkn, subst0, ssubst
            ) where

import Prelude hiding (length, elem,foldl)
import Basics 
import Display
import Data.Sequence hiding (zip,replicate,reverse)
import Control.Arrow (second)
import Data.Foldable
import Permutation

data Term :: * where
     Hole :: Irr Position -> String -> Term -- placeholder
     Star :: Irr Position -> Sort -> Term -- sort
     Bound :: Irr Position -> BitVector -> Int -> Term -- variable
     Pi :: Binder -> Ident -> Cube Term -> Term -> Term 
     Sigma :: Ident -> Term -> Term -> Term
     Lam :: Binder -> Ident -> Cube Term -> Term -> Term 
     Pair :: Ident -> Term -> Term -> Term 
     App :: Binder -> Term -> Cube Term -> Term
     Proj :: Bool {- 1st projection? -} -> Term -> String -> Term     

     -- term such that its relational interpretation is its argument.
     OfParam :: Ident -> Term -> Term 
     
     -- Type annotation. Not present in normal forms.
     Ann :: Term -> Term -> Term 
     
     -- shift the sorts of the terms. Not present in normal forms.
     Shift :: Sort -> Term -> Term 

     -- relational interpretations and world destruction.  In normal
     -- form, arguments to these are either themselves or a variable.
     Param :: Term -> Term 
     Swap :: Permutation -> Term -> Term 
     Destroy :: Int -> Term -> Term

termPosition :: Term -> Irr Position 
termPosition (Hole p _) = p
termPosition (Star p _) = p
termPosition (Bound p _ _) = p
termPosition (Pi _ i _ _) = identPosition i
termPosition (Sigma i _ _) = identPosition i
termPosition (Lam _ i _ _) = identPosition i
termPosition (Pair i _ _) = identPosition i
termPosition (App _ x y) = termPosition x
termPosition (Proj _ x _) = termPosition x
termPosition (Ann x _) = termPosition x
termPosition (Param x) = termPosition x
termPosition (Swap _ x) = termPosition x
termPosition (OfParam _ x) = termPosition x
termPosition (Shift _ x) = termPosition x
termPosition (Destroy _ x) = termPosition x

{-
bound = Bound dummyPosition

-- | Hereditary application
-- invariant: preserves normal forms 
app :: Term -> Term -> Term 
app (Lam i _ bo) u = subst0 u bo
app neutral u = neutral `App` u

subst0 :: Term -> Term -> Term
subst0 u = subst (u:map bound [0..])  

type Subst = [Term]



-- | Hereditary substitution
subst :: Subst -> Term -> Term
subst f t = case t of
  Bound _ x -> f !! x
  Lam i ty bo -> Lam i (s ty) (s' bo)
  Pi i a b -> Pi i (s a) (s' b)
  Sigma i a b -> Sigma i (s a) (s' b)
  (a `App` b) -> (s a) `app` (s b)
  (Ann e t) -> Ann (s e) (s t)
  (Pair i x y) -> Pair i (s x) (s' y)
  (Proj x f) -> proj (s x) f
  (Extr x f) -> extr (s x) f
  Hole p x -> Hole p x
  Star p x -> Star p x
  Param arity x -> param0 arity (s x)
  OfParam i x -> OfParam i (s x)
  Shift f x -> ssubst f (s x)
  Destroy i x -> Destroy i (s x) -- need to move to sort annotated terms to do this correctly. 
  
 where s' = subst (bound 0 : map wk f)
       s  = subst f

-- | Non-hereditary substitution
subst' :: Subst -> Term -> Term
subst' f t = case t of
  Bound _ x -> f !! x
  Lam i ty bo -> Lam i (s ty) (s' bo)
  Pi i a b -> Pi i (s a) (s' b)
  Sigma i a b -> Sigma i (s a) (s' b)
  (a `App` b) -> (s a) `app` (s b)
  (Ann e t) -> Ann (s e) (s t)
  (Pair i x y) -> Pair i (s x) (s' y)
  (Proj x f) -> Proj (s x) f
  (Extr x f) -> Extr (s x) f
  Hole p x -> Hole p x
  Star p x -> Star p x
  Param arity x -> Param arity (s x)
  OfParam i x -> OfParam i (s x)
  Shift f x -> Shift f (s x)
  Destroy i x -> Destroy i (s x)
  
 where s' = subst (bound 0 : map wk f)
       s  = subst f


wkn n = subst' (map bound [n..])
wk = wkn 1
str = subst0 (Hole dummyPosition "oops!")

-- | Hereditary projection
proj (Extr x f')   f | f /= f' = proj x f
proj (Pair (Irr (Identifier (_pos,f'))) x y) f 
  | f == f' = x
   | f /= f' = proj (str y) f
proj x f = Proj x f

-- | Hereditary extraction
extr (Pair (Irr (Identifier (_pos,f'))) x y) f | f == f' = str y
extr x f = Extr x f

-}

deriving instance Show (Term)
deriving instance Eq (Term)

dec xs = [ x - 1 | x <- xs, x > 0]

allFreeVars :: Cube Term -> [Int]
allFreeVars = Prelude.concat . fmap freeVars . cubeElems

freeVars :: Term -> [Int]
freeVars (Ann a b) = freeVars a <> freeVars b
freeVars (Pi _ _ a b) = allFreeVars a <> (dec $ freeVars b)
freeVars (Sigma _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (Bound _ _ x) = [x]
freeVars (App _ a b) = freeVars a <> allFreeVars b
freeVars (Lam _ _ ty b) = allFreeVars ty <> (dec $ freeVars b)
freeVars (Star _ _) = mempty
freeVars (Hole _ _) = mempty
freeVars (Pair _ x y) = freeVars x <> (dec $ freeVars y)
freeVars (Proj _ x _) = freeVars x
freeVars (Param x) = freeVars x
freeVars (Swap _ x) = freeVars x
freeVars (OfParam _ x) = freeVars x
freeVars (Shift _ x) = freeVars x
freeVars (Destroy _ x) = freeVars x

iOccursIn :: Int -> Term -> Bool
iOccursIn x t = x `elem` (freeVars t)

----------------------------
-- Display

cPrint :: Int -> DisplayContext -> Term -> Doc
cPrint p ii (Destroy i x) = cPrint p ii x <> "%" <> pretty i
-- cPrint p ii (Shift (Sort l) x) = cPrint 6 ii x <> text (replicate l '^')                                    -- "⇧" <> prettySortNam o
cPrint p ii (Param x) = cPrint p ii x <> "!"
cPrint p ii (Swap q x) = cPrint p ii x <> "#" <> pretty q
cPrint p ii (OfParam i x) = pretty i
                             -- "⌊" <> cPrint (-1) ii x <> "⌋"
cPrint p ii (Hole _ x) = text x
cPrint p ii (Star _ i) = pretty i
cPrint p ii (Bound _ bv k) 
  | k < 0 || k >= length ii  = text "<deBrujn index" <+> pretty k <+> text "out of range>"
  | otherwise = pretty (ii `index` k) <> subscriptPrettyBV bv
cPrint p ii (Proj True x f)     = cPrint p ii x <> "#" <> text f
cPrint p ii (Proj False x f)     = cPrint p ii x <> "/" <> text f
cPrint p ii t@(App _ _ _)     = let (fct,args) = nestedApp t in 
                                 parensIf (p > 3) (cPrint 3 ii fct <+> sep (map (cPrintCube 4 ii) args))
cPrint p ii (Pi o name d r)    = parensIf (p > 1) (sep [printBind ii name d r <+> arrow o, cPrint 1 (name <| ii) r])
                                 
cPrint p ii (Sigma name d r) = parensIf (p > 1) (sep [printBind ii name (unit d) r <+> cross Regu,  cPrint 1 (name <| ii) r])
cPrint p ii (t@(Lam _ _ _ _))   = parensIf (p > 1) (nestedLams ii mempty t)
cPrint p ii (Ann c ty)      = parensIf (p > 0) (cPrint 1 ii c <+> text ":" <+> cPrint 0 ii ty)
cPrint p ii (Pair name (OfParam _ x) y) 
                            = parensIf (p > (-1)) (sep ["⟦"<>pretty name<>"⟧" <+> text "=" <+> cPrint 0 ii x <> comma, cPrint (-1) (name <| ii) y])
cPrint p ii (Pair name x y) = parensIf (p > (-1)) (sep [pretty name <+> text "=" <+> cPrint 0 ii x <> comma, cPrint (-1) (name <| ii) y])

nestedLams :: DisplayContext -> Seq Doc -> Term -> Doc
-- nestedLams ii xs (Lam o x (Hole _ _) c) = nestedLams (x <| ii) (xs |> pretty x) c
nestedLams ii xs (Lam o x ty c) = nestedLams (x <| ii) (xs |> parens (pretty x <+> colon o <+> cPrintCube 0 ii ty)) c
nestedLams ii xs t         = (text "\\ " <> (sep $ toList $ xs) <+> text "->" <+> nest 3 (cPrint 0 ii t))

printBind ii name d r = case not (isDummyId name) ||  0 `iOccursIn` r of
                  True -> parens (pretty name <+> colon Regu <+> cPrintCube 0 ii d)
                  False -> cPrintCube 2 ii d

cPrintCube p ii d | dim d == 0 = cPrint p ii (d !? nil)
                 | otherwise = "{" <> sep (punctuate ";" [pretty i <> "↦" <> cPrint 0 ii x | (i,x) <- cubeAssocs d]) <> "}"

nestedApp :: Term -> (Term,[Cube Term])
nestedApp (App _ f a) = (second (++ [a])) (nestedApp f)
nestedApp t = (t,[])

prettyTerm = cPrint (-100)

instance Pretty Term where
    pretty = prettyTerm mempty

{-
---------------------------------------------------------------
-- Sort substitution

ssubst :: Sort -> Term -> Term
ssubst f t = case t of
  Bound p x -> Shift f (Bound p x)
  Lam i ty bo -> Lam i (s ty) (s bo)
  Pi i a b -> Pi i (s a) (s b)
  Sigma i a b -> Sigma i (s a) (s b)
  (a `App` b) -> (s a) `App` (s b)
  (Ann e t) -> Ann (s e) (s t)
  (Pair i x y) -> Pair i (s x) (s y)
  (Proj x f) -> Proj (s x) f
  (Extr x f) -> Extr (s x) f
  Hole p x -> Hole p x
  Star p x -> Star p (f + x)
  Param arity x -> Param arity (s x)
  OfParam i x -> OfParam (modId (++ show f) i) (s x)  
  Shift f' x -> ssubst (f + f') x
  Destroy f x -> Destroy f (s x)
 where s = ssubst f

---------------------------------------------------------------
-- Hereditary parametricity transform

type Env = [Subst]

renam :: Env -> Int -> Term -> Term
renam g idx a = ssubst nextRel $ subst (g !! idx) a

re :: Int -> Ident -> Ident
re idx = modId (++ subscriptShow idx)

param0 arity = param arity (map (Param arity . bound) [0..] : replicate arity (map bound [0..]))

-- | Transform a term to its relational interpretation
param :: Int -> Env -> Term -> Term
param arity = paramProg
  where
  extCtx gs = [bound idx:map (wkn (arity + 1)) g | (idx,g) <- zip (0:reverse [1..arity]) gs]
    
  paramProg :: Env -> Term -> Term
  paramProg g (Shift f x) = Shift f (paramProg g x) 
  paramProg g (Destroy f x) = Param arity (Destroy f x)
  paramProg g (Hole p s) = Hole p ("[" ++ s ++ "]")
  paramProg g (Bound p x) = g !! 0 !! x
  paramProg g (Lam i ty bo) = paramBind g Lam  i ty $
                          paramProg (extCtx g) bo
    
  paramProg g (Pair i x y) = 
     Pair i (paramProg g x) 
            (paramProg (map (\d -> Hole dummyPosition "pair not in nf!":map wk d) g) y)
     -- because the input is in normal form, the variable bound by the
     -- pair can never appear in y.
  paramProg g (f `App` a) = foldl app (paramProg g f) [renam g idx a | idx <- [1..arity]] `app` paramProg g a
  paramProg g (Proj e f) = proj (paramProg g e) f
  paramProg g (Extr e f) = extr (paramProg g e) f
  paramProg g (Ann _ _) = error "Ann should not be in nf term"
  paramProg g (OfParam i x) = case arity of
      0 -> OfParam (modId (\x -> "⌈" ++ x ++ "⌉") i) (paramProg g x)                                
      1 -> x `app` ssubst nextRel (OfParam i x) 
      _ -> error "mismatch in arity not yet supported"
  paramProg g x@(Param _ _) = Param arity x -- FIXME: here the renaming substitution should be applied;
                              -- but applying the current substitution has the effect of swapping the params.
  paramProg g ty = appl [Lam (synthId $ "z" ++ subscriptShow i) (wkn (i-1) $ renam g i ty) | i <- [1..arity] ] (zerInRel g ty)

  appl :: [a -> a] -> a -> a
  appl []     x = x
  appl (f:fs) x = f (appl fs x)

  -- | Build a relation witnessing x ∈ ⟦ty⟧. (where 'x' is not bound in 'ty'.)
  zerInRel :: Env -> Term -> Term
  zerInRel gs ty = inParam (map (map (wkn arity)) gs) ty (reverse $ map bound [0..arity-1])

  -- | Build a relation z ∈ ⟦ty⟧.  z is a term that, after renaming,
  -- gives the vector of terms member of the relation.  Note that
  -- 'param' is never applied to 'z', therefore 'zR' never occurs in the result.

  inParam :: Env -> Term -> [Term] -> Term
  inParam g (Star  p s)   zs = appl [Pi dummyId (wkn i z) | (i,z) <- zip [0..] zs] (Star p s)
  inParam g (Pi    i a b) zs = paramBind g Pi i a (inParam (extCtx g) b 
                                                  [(wkn (arity + 1) z `app` bound i) | (i,z) <- zip (reverse [1..arity]) zs])

  inParam g@(g0:gs) (Sigma name@(Irr (Identifier (_,f))) a b) zs = 
    Sigma name (inParam g a (map (`proj` f) zs))
    (inParam ((bound 0:map wk g0):[(proj (wk z) f):map wk g2 | (g2,z) <- zip gs zs]) b [(Extr (wk z) f) | z <- zs])
  -- z ∈ ⟦(x : A) × B(x)⟧ =   (x : π₁ z ∈ ⟦A⟧) × π₂ z ∈ ⟦B(x)⟧

  inParam g (Sigma _ _ _) z = error "Σ not implemented"
  inParam g t z = foldl app (paramProg g t) z

  -- | Translate a binding (x : A) into (x₁ : A₁) (⟦x⟧ : ⟦A⟧ x₁)
  paramBind :: Env -> (Ident -> Term -> Term -> Term) -> Ident -> Term -> Term -> Term
  paramBind g binder name a rest = 
      appl 
      [binder (re i name) (wkn (i-1) $ renam g i a) | i <- [1..arity]] $
      binder name         (zerInRel g a) $ 
      rest 

nextRel = Sort 0 1
nxt = ssubst nextRel

--------------------------
-- destruction of worlds


destruction :: Int -> Seq Bool -> Term -> Maybe Term
destruction destroyed d t = case t of
  (Hole p x)  -> Just $ Hole p ("|" ++  x ++ "|")
  (Bound p x)  
    | x >= Data.Sequence.length d -> Just (Bound p x)  
    -- FIXME: this is incorrect; instead the callers of this function
    -- must give the correct value for variables of the environment.
    | otherwise -> if d `index` x then Just (Bound p x) else Nothing
  (Star p (Sort l w))  
      | w >= destroyed -> Nothing
  (Star p (Sort l r))  -> Just $ Star p (Sort l r)
  (Pi i a b)  -> mb d Pi i a b 
  (Sigma i a b)  -> mb d Sigma i a b 
  (Lam i ty bo)  -> mb d Lam i ty bo  
  (Pair i a b)  -> mb d Pair i a b 
  (Ann e t)  -> Ann <$> pr e <*> pr t 
  (a `App` b)  -> case pr b of
                   Nothing -> pr a
                   Just b' -> (`App` b') <$> pr a 
  (Proj x f) -> (\x -> Proj x f) <$> pr x  
  (Extr x f) -> (\x -> Extr x f) <$> pr x  
  
  -- FIXME: This should traverse the potential series of Param to find if the variable is removed.
  (Param arity (Bound p x)) | x < Data.Sequence.length d && not (d `index` x) -> Nothing
  -- Just a "renaming" on NFs: x should be a (renamed) variable.
  (Param arity x) -> Just (Destroy destroyed (Param arity x))
  (Shift f x)    ->  Just (Destroy destroyed (Shift f x))
   
  (OfParam n x) -> OfParam (modId (++ "%" ++ show destroyed) n) <$> pr x
  

 where mb d binder i a b = case pr a of
                             Nothing -> str <$> destruction destroyed (False <| d) b
                             Just a' -> binder i a' <$> destruction destroyed (True <| d) b
       pr x = destruction destroyed d x

-- pr (Param x) d = Just x FIXME: there is a problem here: 1st
-- order variables have been removed, so we cannot refer to them.


  
-}