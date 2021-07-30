
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Arrow for function types                                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// arrow[->]
arr_fun : forall a. a -> a
  = \x. x  
;

// f >>> g
arr_seq_fun : forall a b c. (a -> b) -> (b -> c) -> a -> c
  = \f g x. g (f x)
;

// f &&& g
arr_par_fun : forall a b c. (a -> b) -> (a -> c) -> a -> (b,c)
  = \ f g x. (f x, g x)
;

////////////////////////////////////////////////////////////////////////////////
// main program
////////////////////////////////////////////////////////////////////////////////

// arr (+)
arr_plus : (Int, Int) -> Int 
  = arr_fun
      (\xy.
        case xy {
	  (x,y) => x + y
	}
      )
;

// f &&& g >>> arr (+)
addA : (Int -> Int) -> (Int -> Int) -> Int -> Int
  = \f g @ client .
     arr_seq_fun 
      (arr_par_fun f g)
      (arr_plus)

;

main : Unit
  = print 
      (intToString 
         (addA (\x @ client . x+1) (\x @ server . x-1) 10))

