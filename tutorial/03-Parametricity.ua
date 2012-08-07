-- Parametricity
-----------------

-- In uAgda every term is known to be parametric.
-- hence for an arbitrary function f...
\(A : *) (B : *) (f : A -> B) -> (

-- we can use the fact that it is parametric by using the postfix '!' operator:
fparam = f! : (x : {A ; A!}) -> B! @ {f (x 0)},

-- Note here that we introduce the cube syntax.
-- {A; A!}   is a 2-element cube; and 
-- x 0       accesses the 1st component of the cube x.

-- We also have an example of an incomplete cube: 
-- {f (x 0)} 

-- In the above, it is inferred to be incomplete thanks to the special
-- application operator: 

-- @ (Relation membership test) 

-- Finally, relation types can be formed using the double arrow:
-- =>

-- Note that, so far, there was no explicit mention of cubes, because
-- a 1-element cube can be just written as its contents. That is, A
-- really stands for {A} in a cube context.

-- See the paper for a detailed explanation of the role of cubes.



*)
