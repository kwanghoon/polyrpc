
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Arrow for function types                                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// arrow[->]
arr_fun
  : {l}. [a]. (a -l-> a)
  = {l}. \x @ l . x  
;

// f >>> g
arr_seq_fun
  : {l1 l2 l3 l4 l5}. [a b c]. ( (a -l1-> b) -l3-> (b -l2-> c) -l4-> a -l5-> c )
  = {l1 l2 l3 l4 l5}.
      \f @ l3
       g @ l4 
       x @ l5 . g (f x)
;

// f &&& g
arr_par_fun 
  : {l1 l2 l3 l4 l5}. [a b c]. ( (a -l1-> b) -l3-> (a -l2-> c) -l4-> a -l5-> (b,c) )
  = {l1 l2 l3 l4 l5}.
      \f @ l3
       g @ l4 
       x @ l5 . (f x, g x)
;

////////////////////////////////////////////////////////////////////////////////
// main program
////////////////////////////////////////////////////////////////////////////////

// arr (+)
arr_plus
  : {l}. ( (Int, Int) -l-> Int )
  = {l}. arr_fun {l} 
      (\xy @ l .
        case xy {
	  (x,y) => x + y
	}
      )
;

// f &&& g >>> arr (+)
addA
  : (Int -client-> Int) -client-> (Int -server-> Int) -client-> Int -client-> Int
  = \f @ client 
     g @ client  .
     arr_seq_fun {client client client client client}
      (arr_par_fun {client server client client client} f g)
      (arr_plus {client})

;

main : Unit
  = print {client}
      (intToString {client} 
         (addA (\x @ client . x+1) (\x @ server . x-1) 10))
	 

