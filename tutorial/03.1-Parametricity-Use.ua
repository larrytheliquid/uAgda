-- let's use parametricity in a useful way: prove that any
-- function of type (X : #) -> X -> X is the identity.

-- To simplify the example we use impredicativity here; the impredicative sort is written #.


-------------------------
-- Preliminaries

-- Type of propositions, at dimension 1. (Optionally, the dimension of
-- a sort is written after a pipe; otherwise it is 0)
prop = #|1, 

-- Truth
Top = (A : #) -> A -> A
    : #,

-- ... and its inhabitant
tt = \A x -> x
   : Top,


---------------------------------------------------
-- Leibniz equality (modified to support cubes.)

-- The regular definition for Leibniz equality is
-- Eq = \A a b -> (P : A -> #) -> P a -> P b

-- We face a number of superficial complications, because we want Eq A
-- a b to be of dimension 1, instead of dimension 0.

-- 1. we must use #|1 instead of #|0;
-- 2. we have to extend quantifications in such a way that they are always over cubes of dimension 1.
--    this is done by adding dummy arguments in cubes (# and Top below)

Eq = \A a b -> (P : {# ; \t => (z : A) => prop} ) -> {Top ; \t => P 1 @ a} -> P 1 @ (b 0)
   : (A : #) -> A -> A => prop
   ,

refl = \A x P p -> p 1
     : (A : #) -> (x : A) -> Eq A x @ x,

-- The theorem is expressed as normal:
Theorem = 
  (f : (A : #) -> A -> A) ->
  (A : #) ->
  (x : A) ->
  Eq A x @ (f A x),

-- The proof follows the usual technique; see the paper for details.
proof = \(f : (A : #) -> (a : A) -> A) ->
        \(A : #) ->
        \(x : A) -> f! {A ; \y => Eq A x @ (y 0) } {x ; refl A x}
      : Theorem,


# 

