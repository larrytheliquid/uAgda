-- Module parametrization, universes, holes.
-----------------------------------------------

-- If you want to parameterize your module (think ML functors), just
-- use top-level abstraction: 

\ (Z : *) (plus : Z -> Z -> Z) -> ( 

-- Note that parentheses are needed here (check operator precedence in
-- the source code: "RawSyntax.hs" contains the syntax in BNF)


-- We define Leibniz equality for good measure:
Eq = \ A a b -> (P : A -> *) -> P a -> P b
     : (A : *) -> (a b : A) -> *1,

-- By default uAgda is predicative, hence Leibniz equality is in 
-- *1.

-- Sometimes you may want to omit the definition for a particular
-- term. (For example you know a theorem to hold but you'd rather
-- write the proof later.)  In that case you can use the "hole"
-- construct as follows. 

plus-commutative = \ (x : Z) (y : Z) -> (?x : Eq Z (plus x y) (plus y x)),

-- Note that uAgda shows the context of the hole, so it's easier to
-- fill it in later.

-- End of tuple.
*)
