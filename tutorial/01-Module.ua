-- Modules, type annotations, Sigma
-------------------------------------

-- Usually you will want to break down your definitions
-- into multiple parts. That can be done by making the
-- top-level term a tuple. 

-- For example, this file starts with:
Nat = (N : *) -> (N -> N) -> N -> N,

-- which declares the 1st component of the tuple, and gives
-- it a name.


-- Let's define some more stuff:
zer = \N s z -> z : Nat,


-- Note that every term may be annotated by its type.  This is good
-- because no type inference is done.  (Even though the system is
-- clever enough to push down type annotations in lambdas)

-- Let's define the standard Church numeral toolbox:


suc = \m N s z -> s (m N s z) 
    : Nat -> Nat,

plus = \n m N s z -> n N s (m N s z)
     : Nat -> Nat -> Nat,

mul = \n m N s -> n N (m N s)
    : Nat -> Nat -> Nat,

exp = \n m N -> m (N -> N) (n N)
    : Nat -> Nat -> Nat,


-- Now we're ready for some calculation! (the results can be seen in
-- the normal form)
one = suc zer,
two = suc one,
four = exp two (mul two two),

-- The syntax for pairs is "first class", we can have them anywhere:
somePair = (pi1 = two, plus two four) : (Nat ;; Nat),


-- Dependent pairs can also be declared
depPair  = (A = Nat, suc) : ((A : *1) ;; A -> A),

-- fields named in the type can be extracted using .:
extract = depPair.A,

-- Finally we must give the last component of the tuple, which is NOT
-- named.  Since we have nothing special in mind, let's just give a
-- random simple term:

*


