{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances, GADTs, PatternGuards, GeneralizedNewtypeDeriving #-}

-- Type checker loosely based on 
--
-- "On the Algebraic Foundation of Proof Assistants for Intuitionistic Type Theory", Abel, Coquand, Dybjer
--
-- some ideas from
--
-- "A Tutorial Implementation of a Dependently Typed Lambda Calculus", Löh, McBride, Swierstra
--
-- are also implemented.
--

module TypeCheckerNF where

import Prelude hiding (length,sequence)
import Basics
import qualified Terms
import Terms (Term (Ann))
import Display
import Control.Monad.Error hiding (sequence)
import Data.Char
import Data.Maybe (isJust)
import Control.Monad.Trans.Error (ErrorT, runErrorT)
import Control.Monad.Writer.Class
import Control.Monad.Writer hiding (sequence, (<>))
import Control.Monad.Trans.State (StateT, execStateT, modify, get)
import Data.Functor.Identity
import Data.Sequence hiding (replicate)
import Data.Foldable (toList,Foldable)
import qualified Data.List as L
import Data.Traversable
import Normal hiding (Term)
import qualified Normal
import Options
import Data.Array.IArray (assocs,array)
import Data.Function
import Debug.Trace
import Permutation (permLength)

instance Error (Term,Doc) where
  strMsg s = (Terms.Hole dummyPosition "strMsg: panic!",text s)

newtype Result a = Result ((ErrorT (Term,Doc)) -- term is used for position information
                          (WriterT [Doc] Identity) a)
    deriving (Functor,Monad, MonadError (Term,Doc), MonadWriter [Doc])

report :: Doc -> Result ()
report x = tell [x]

runChecker :: Result a -> (Either (Term,Doc) a,[Doc])
runChecker (Result x) = runIdentity $ runWriterT $ runErrorT x

data Definition = Abstract -- ^ lambda, pi, sigma bound
                | Direct Value -- ^ pair bound

type Value    = NF
type Type     = Value
type Dimension = Int
data Bind     = Bind {entryIdent :: Ident, 
                      entryValue :: Definition, -- ^ Value for identifier. 
                      entryType :: Cube Type,    -- ^ Attention: context of the type does not contain the variable bound here.
                      entryBinder :: Binder
                     }
type Context  = Seq Bind

display :: Context -> NF -> Doc
display c = prettyTerm (fmap entryIdent c)

displayT :: Context -> Term -> Doc
displayT = Terms.prettyTerm . fmap entryIdent

dispContext :: Context -> Doc
dispContext ctx0 = case viewl ctx0 of
  EmptyL -> mempty
  Bind x val typ o :< ctx0' -> (let ctx' = fmap entryIdent ctx0'
                                in case val of
    Abstract   ->             pretty x <+>                                        colon o <+> printCube o 0 ctx' typ
    Direct   v ->             pretty x <+> sep ["=" <+> parens (cPrint 0 ctx' v), colon o <+> printCube o 0 ctx' typ]
    ) $$ dispContext ctx0'

todo = Regu -- for now sigma types are always of the "complete" cube kind.

resurrect :: Binder -> Context -> Context
resurrect _ = id

subCubeAt' bv c = updateCube (ones $ dim c) (hole "⊘") $ subCubeAt bv c

iType :: Context -> Term -> Result (Value,Type,Dimension)
iType g (Ann e tyt)
  =     do  (ty,o) <- iSort g tyt 
            (v,d) <- cType g e ty
            return (v,ty,d) -- annotations are removed
iType g t@(Terms.Star p s)
   =  return (Star s,Star $ above s, 0)  
iType g (Terms.Pi r1 ident tyt tyt')  
   =  do  (ty ,s1) <- iSortCube r1 (resurrect Regu g) tyt 
          (ty',s2) <- iSort (Bind ident Abstract ty r1 <| g) tyt'
          let o = s1 ⊔ s2
          return (Pi r1 ident ty ty', Star o, 0)
iType g (Terms.Sigma ident tyt tyt')  
   =  do  (ty,s1)  <- iSort (resurrect Regu g) tyt 
          let r1 = todo
          (ty',s2) <- iSort (Bind ident Abstract (unit ty) r1 <| g) tyt'
          let o = s1 ⊔ s2
          return (Sigma r1 ident ty ty', Star o, 0)
iType g e@(Terms.Bound _ bv x) = do
  when (bvDim bv /= dim typ0) $ 
       throwError (e,"inexact cube access: expected dimension " <> pretty (dim typ0) )
  return $ (val $ value, finalTyp, setBits bv)
  where val (Direct v) = wkn (x+1) v
        val _ = Neu $ Var $ V bv x
        typ = cubeAccess "iType var" typ0 bv
        arg = updateCube (ones da) (hole  "⊘") arg0
        arg0 = subCubeAt bv $ fullVarCube x (dim typ0)
        finalTyp = app Pred (wkn (x+1) typ) arg
        da = dim arg0
        Bind _ value typ0 o = g `index` x
        
iType g (Terms.Hole p x) = do
  report $ hang (text ("context of " ++ x ++ " is")) 2 (dispContext g)
  return (hole x, hole ("type of " ++ x),0)
iType g (Terms.App o' e1 e2)
  =     do  (v1,ti,d) <- iType g e1
            case ti of
              Pi o _ ty ty' -> do 
                   when (o /= o') $ throwError (e1,"application: non-matching binder kinds")
                   v2 <- cTypeCube o (resurrect o g) e2 ty
                   return (app o v1 v2, subst0 v2 ty',d)
              _             ->  throwError (e1,"invalid application")
iType g (Terms.Proj isFirst e f) = do
  (v,t,_) <- iType g e
  search v t
 where search :: NF -> NF -> Result (Value,Type,Dimension)
       search v (Sigma o i ty ty') 
              | f == f' = return $ if isFirst then (π1,ty,0) else (π2,subst0 (unit π1) ty',0)
              | otherwise = search π2 (subst0 (unit π1) ty')
           where 
                 f' = idString i
                 (π1,π2) = (case v of
                             Pair _ _ x y -> (x,y) -- substitution is useless if the pair is in normal form.
                             _ -> (proj o v True i,proj o v False i)  -- This could not happen if eta-expansion were done.
                             ) :: (NF,NF)
       search _ _ = throwError (e,"field not found")

iType g (Terms.Pair ident e1 e2) = do
  (v1,t1,_) <- iType g e1
  let r1 = todo
  (v2,t2,_) <- iType (Bind ident (Direct v1) (unit t1) r1 <| g) e2
  return $ (Pair r1 ident v1 (str v2),Sigma r1 ident t1 t2,0)
-- Note: the above does not infer a most general type: any potential dependency is discarded.

iType g t@(Terms.Lam o x h e) 
   | dim h == 0, (Terms.Hole _ _) <- h !? nil
   = throwError (t,"cannot infer type for" <+> displayT g t)
iType g (Terms.Lam o x ty e) = do
    (vty,vs) <- iSortCube o (resurrect Regu g) ty
    (ve,t,d) <- iType (Bind x Abstract vty o <| g) e
    return $ (Lam o x vty ve, Pi o x vty t,min d (dim vty))

iType g (Terms.Param e) = do
  (v,t,d) <- iType g e
--  report $ "param: " <> vcat [displayT g e, display g t, display g (param Thing t)]
  return (param Thing v, inTrans [] t v,1+d)

iType g (Terms.Swap q e) = do
  (v,t,d) <- iType g e
  when (d /= permLength q) $ 
    throwError (e,"swapped term has wrong dimension: " <> pretty d)
  return (swap q v, swap q t,d)


iSort :: Context -> Term -> Result (Type,Sort)
iSort g e = do
  (val,v,_) <- iType g e
  case v of 
    Star i -> return (val,i)
    (Neu (Var (Hole (Irr h)))) -> do 
         report $ text h <+> "must be a type"
         return $ (hole h, Sort 1 0)
    _ -> throwError (e,displayT g e <+> "is not a type. Instead: " <+> display g v)

iSortCube' :: Int -> Context -> Term -> BitVector -> StateT (Cube Type) Result ()
iSortCube' s g e i = do
  types <- get
  t <- fst <$> (lift $ cType g e (Pi Pred dummyId (subCubeAt i types) (Star $ Sort s $ setBits i)))
  modify (updateCube i t)


-- | Return the cube contents, stuff on the "lower" corner first. Top
-- corner excluded if Pred cube.
cubeContents :: Binder -> Cube a -> [(BitVector,a)]
cubeContents o = L.sortBy (compare `on` (setBits . fst)) . tweak o . assocs

iSortCube :: Binder -> Context -> Cube Term -> Result (Cube Type,Sort)
iSortCube o g c = do
  (t0,Sort l _) <- iSort g (c !? zeros (dim c))
  
  ts <- execStateT (sequence [iSortCube' l g a i | (i,a) <- L.drop 1 $ -- exclude the lower corner, as it's not a Pi here. (and already checked)
                                                            cubeContents o c])
                   (updateCube (zeros (dim c)) t0 $ full (const $ hole "⊘") (dim c))
  return (ts,Sort l (dim c)) 
 where d = dim c

unify :: Context -> Term -> Type -> Type -> Result ()
unify g e q q' =
         do let ii = length g
                constraint = report $ vcat ["constraint: " <> display g q',
                                            "equal to  : " <> display g q]
            case (q,q') of
              ((Neu (Var (Hole _))), t) -> constraint
              (t, Neu (Var (Hole _))) -> constraint
              _ -> unless (q == q') 
                       (throwError (e,hang "type mismatch: " 2 $ vcat 
                                             ["inferred:" <+> display g q',
                                              "expected:" <+> display g q ,
                                              -- "q'" <+> text (show q'),
                                              -- "q " <+> text (show q),
                                              "for:" <+> displayT g e ,
                                              "context:" <+> dispContext g]))

unifyAll :: Binder -> Context -> Term -> Cube Type -> Cube Type -> Result ()
unifyAll o g e q q' = do
  when (dim q /= dim q') $ throwError (e,"non-matching dimensions")
  -- FIXME: skip if Pred
  sequence_ $ tweak o $ Prelude.zipWith (unify g e) (cubeElems q) (cubeElems q')

-- Check the type and normalize
cType :: Context -> Term -> Type -> Result (Value,Dimension)
cType g (Terms.Lam _ name h e) (Pi o name' ty ty') | dim h == 0, (Terms.Hole _ _) <- h !? nil = do
        (e',d) <- cType (Bind name Abstract ty o <| g) e ty'
        return (Lam o name ty e',min d (dim ty)) -- the type and binder is filled in.

cType g e0@(Terms.Lam o' name ty0 e) (Pi o name' ty ty')
  =     do when (o /= o') $ throwError (e0,"Unmatching flavours of quantification")
           (t,_o) <- iSortCube o (resurrect o g) ty0
           unifyAll o g (Terms.Hole (identPosition name) (show name)) t ty
           (e',d) <- cType (Bind name Abstract ty o <| g) e ty'
           return (Lam o name ty e',min d (dim ty))

cType g (Terms.Pair name e1 e2) (Sigma o name' ty ty') = do
  -- note that names do not have to match.
  (v1,d1) <- cType g e1 ty           
  (v2,d2) <- cType (Bind name (Direct v1) (unit ty) o <| g) e2 (wk $ subst0 (unit v1) ty') 
        -- The above weakening is there because:
        -- * the type contains no occurence of the bound variable after substitution, but
        -- * the context is extended anyway, to bind the name to its value.
  return (Pair o name' v1 (str v2),min d1 d2)
  -- note that the pair must use the name of the sigma for the
  -- field. (The context will use the field name provided by the type)
{-
--  Γ ⊢ ⌊A⌋ : B
cType g (Terms.OfParam i e) t = do
  -- Γ ⊢ A ⌊A⌋ : ⟦B⟧ ⌊A⌋
  -- Γ ⊢ A x   : ⟦B⟧ x
  -- Γ ⊢ A     : (x : ⌊B⌋) → ⟦B⟧ x
  e' <- cType g e $ Pi Ty i t (zerInRel 0 t)
  return (Neu $ OfParam i e')
-}

cType g e v 
  =     do (e',v',d) <- iType g e
           unify g e v v'
           return (e',d)


cTypeCube' :: Context -> Term -> Cube Type -> BitVector -> StateT (Cube Value) Result ()
cTypeCube' g e t i = do
  values <- get
  v <- fst <$> (lift $ cType g e (app Pred (t !? i) (subCubeAt i values)))
  modify (updateCube i v)
             
tweak Regu = id
tweak Pred = init

cTypeCube :: Binder -> Context -> Cube Term -> Cube Type -> Result (Cube Value)
cTypeCube o g e t = do
  when (dim e /= dim t) $ 
       throwError (cubeFirstElemForErr e,"type cube: non-matching dimensions")
  execStateT (sequence [cTypeCube' g a t i | (i,a) <- cubeContents o e])
             (full (const $ hole "⊘") (dim e))


cubeFirstElemForErr :: Cube Term -> Term
cubeFirstElemForErr c = (cubeElems c ++ [error "empty cube!"]) !! 0
  
