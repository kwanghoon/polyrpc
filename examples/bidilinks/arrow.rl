
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
arr_plus : (Int, Int) -> Int    // Todo: Just by {l} (Int,Int) -> Int cannot create /\l. !!
  = \p. arr_fun                 //       Introduce an eta exapnsion to create /\l. !!
      (\xy.
        case xy {
	  (x,y) => x + y
	}
      ) p
;

// f &&& g >>> arr (+)
addA : (Int -> Int) -> (Int -> Int) -> Int -> Int
  = \f g .
     arr_seq_fun 
      (arr_par_fun f g)
      (arr_plus)

;

main : Unit
  = print 
      (intToString 
         (addA (\client: x. x+1) (\server: x. x-1) 10))

