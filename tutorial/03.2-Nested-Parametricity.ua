-- nested parametricity example from the paper.


\(A : *) ->

( 
  parametricity = \(x:A) -> x!
                : (x:A) -> A! @ {x},

  nested = parametricity!
         : (x : {A; A!}) -> A!! @ {x 0;x 1;x 0!},
  
  nestedNF = \ (x : {A; A!}) -> x 1 ! #10
           :   (x : {A; A!}) -> A!! @ {x 0;x 1;x 0!},
         

*
)