{-# LANGUAGE PackageImports #-}

module AbsSynToTerm where

import Terms 
import qualified RawSyntax as A
import RawSyntax (Identifier(..))
import Control.Monad.Trans.State (runStateT, StateT)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error
import Control.Monad.State
import Control.Applicative
import Data.Functor.Identity
import Data.List
import Basics
import Permutation
import Data.List.Split

type LocalEnv = [String]
type GlobalEnv = ()

type Resolver a = ReaderT LocalEnv (StateT GlobalEnv (ErrorT String Identity)) a


runResolver :: Resolver a -> a
runResolver x = case runIdentity $ runErrorT $ runStateT (runReaderT x []) () of
                  Left err -> error err
                  Right a -> fst a

look :: BitVector -> Identifier -> Resolver Term
look bv (ident@(Identifier (position,x))) = do
  e <- ask
  case elemIndex x e of
    Nothing -> throwError ("unknown identifier: " ++ show ident)
    Just x -> return $ Bound (Irr position) bv x

insertVar :: Identifier -> LocalEnv -> LocalEnv
insertVar (Identifier (_pos,x)) e = x:e

dummyVar :: Identifier
dummyVar = Identifier ((0,0),"_")


manyDep o binder a []     b = resolveTerm b
manyDep o binder a (x:xs) b = binder (Irr x) <$> resolveMulti o a <*> local (insertVar x) (manyDep o binder a xs b)

manyLam :: [A.Bind] -> A.Exp -> Resolver Term
manyLam []            b = resolveTerm b
manyLam (A.NoBind (A.AIdent x):xs) b = Lam Regu (Irr x) (unit $ Hole dummyPosition "") <$> local (insertVar x) (manyLam xs b)
manyLam (A.Bind (A.AIdent x) (A.Colon o) t:xs) b = Lam (toBnd o) (Irr x) <$> resolveMulti (toBnd o) t <*> local (insertVar x) (manyLam xs b)

toBnd ":" = Regu
toBnd "::" = Pred

extractVars :: A.Exp -> Resolver [Identifier]
extractVars (A.EVar (A.AIdent i)) = return [i]
extractVars (A.EApp (A.EVar (A.AIdent i)) rest) = (i:) <$> extractVars rest
extractVars _ = throwError "list of variables expected"

trailingHole Regu xs = xs
trailingHole Pred xs = xs ++ [Hole (Irr (0,0)) "⊘"]

resolveMulti :: Binder -> A.Exp -> Resolver (Cube Term)
resolveMulti o t = do
  xs <- trailingHole o <$> resolveMulti' t
  case cubeFromList xs of
    Just c -> return c
    Nothing -> throwError "incomplete cube"

resolveMulti' :: A.Exp -> Resolver [Term]
resolveMulti' (A.EMulti xs) = mapM resolveTerm xs
resolveMulti' x = (:[]) <$> resolveTerm x

resolveTerm :: A.Exp -> Resolver Term
resolveTerm (A.EMulti _) = throwError "expression list only allowed in some contexts"
-- resolveTerm (A.EDestr x (A.Natural n)) = Destroy (read n) <$> resolveTerm x
resolveTerm (A.EHole (A.Hole (p,x))) = return $ Hole (Irr p) x
resolveTerm (A.EParam x) = Param <$> resolveTerm x
resolveTerm (A.ESwap x (A.Permutation ('#':p))) = Swap (permFromString p) <$> resolveTerm x
-- resolveTerm (A.EUp x) = Shift (Sort 1) <$> resolveTerm x
resolveTerm (A.EVar (A.AIdent x)) = look nil x
resolveTerm (A.EVarI (A.AIdent x) (A.Natural ix)) = look (bvFromString ix) x
resolveTerm (A.ESet (A.Sort (p,c:s))) = return $ Star (Irr p) $ Sort level (read ('0':dim))
   where (lev:dim:_) = splitOn "|" s ++ [""]
         level = case c of
                   '#' -> (-1)
                   '*' -> read ('0':lev)
resolveTerm (A.EProj x (A.AIdent (Identifier (_,field)))) = Proj True  <$> resolveTerm x <*> pure field
resolveTerm (A.EExtr x (A.AIdent (Identifier (_,field)))) = Proj False <$> resolveTerm x <*> pure field
resolveTerm (A.EApp f x)  = App Regu <$> resolveTerm f <*> resolveMulti Regu x
resolveTerm (A.EAppP f x) = App Pred <$> resolveTerm f <*> resolveMulti Pred x
resolveTerm (A.ESigma a b) = case a of
   (A.EAnn vars colon a') -> do
     vs <- extractVars vars
     manyDep Regu (\i a b -> Sigma i (a!?nil) b) a' vs b
                          
   (A.EAbs _ _ _) -> throwError "cannot use lambda for type"
   _              -> Sigma (Irr dummyVar) <$> resolveTerm a <*> local (insertVar dummyVar) (resolveTerm b)            
resolveTerm (A.EPi a (A.Arrow arrow) b) = case a of
   (A.EAnn vars (A.Colon colon) a') -> do 
     vs <- extractVars vars
     manyDep o (Pi o) a' vs b
                          
   (A.EAbs _ _ _) -> throwError "cannot use lambda for type"
   _            -> Pi o (Irr dummyVar) <$> resolveMulti o a <*> local (insertVar dummyVar) (resolveTerm b)

 where o = case arrow of
             "->" -> Regu
             "=>" -> Pred

resolveTerm (A.EAbs ids _ b) = manyLam ids b
resolveTerm (A.EPair (A.Decl (A.AIdent i) e) rest) = Pair (Irr i) <$> resolveTerm e <*> local (insertVar i) (resolveTerm rest)
resolveTerm (A.EPair (A.PDecl (A.AIdent i) e t) rest) = 
   Pair (Irr i) <$> 
   (Ann <$> (OfParam (Irr i) <$> resolveTerm e) <*> resolveTerm t)
   <*> local (insertVar i) (resolveTerm rest)

resolveTerm (A.EAnn e1 _colon_ e2) = Ann <$> resolveTerm e1 <*> resolveTerm e2

