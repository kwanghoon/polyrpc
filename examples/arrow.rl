
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

// // f &&& g
arr_par_fun : forall a b c. (a -> b) -> (a -> c) -> a -> (b,c)
  = \ f g x. (f x, g x)
;

////////////////////////////////////////////////////////////////////////////////
// main program
////////////////////////////////////////////////////////////////////////////////

// arr (+)
arr_plus : (Int, Int) -> Int    // Todo: Just by {l} (Int,Int) -> Int cannot create /\l. !!
  = \p. arr_fun                 //       Introduce an eta exapnsion to create /\l. !!
      (\xy.                     // arr_fun {?1} [... -?2-> ...] (\xy@?3. ...) 
        case xy {               //  ?1, ?2 == ?3 but no more constraint!
	  (x,y) => x + y        //  We can set the location (\p. ...) to them 
	}                       //  by having a priority on local application!
      ) p
;

// f &&& g >>> arr (+)
addA : client: (Int -> Int) -> (Int -> Int) -> Int -> Int
  = \f g .
     arr_seq_fun 
      (arr_par_fun f g)
      (arr_plus)

;

// main : Unit = (print { 'l_v^ })
//   ((intToString { 'l_w^ })
//     ((addA { client })
//       (\client: x : Int . x + {client } 1)
//       (\client: y : Int . (\server: x : Int . x - {server } 1) y)
//       10))


main : Unit                                 // print {?1} and intToString {?2}
  = print                                   // ?1 and ?2 are unconstrained, so 
      (intToString                          // we can set the current location (client) to them
                                            // by having a priority on local application!
         (addA (\client: x. x+1) (\client: y. (\server: x. x-1) y) 10)) // Interesting!!

