// arrow[->]
arr_fun : forall a. a -> a
  = \x. x  
;

arr_plus : (Int, Int) -> Int    // Todo: Just by {l} (Int,Int) -> Int cannot create /\l. !!
  = \p. arr_fun                 //       Introduce an eta exapnsion to create /\l. !!
      (\xy.
        case xy {
	  (x,y) => x + y
	}
      ) p

