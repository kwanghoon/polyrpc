

// ------------------------
// Testcase: Case/Con/Tuple
// ------------------------

data List = [a]. Nil | Cons a (List [a])  ;

map : {l1 l2}. [a b]. ((a -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}.
      \f @l2 xs @l2 .
        case xs {
	 Nil => Nil;
         Cons y ys => Cons (f y) (map {l1 l2} f ys)
	};
	
	
main : List [Int] 
     = map {client server}
         (\x @client . x + 5) (Cons 1 (Cons 2 (Cons 3 (Nil))))
