
data List = [a]. Nil | Cons a (List [a])  ;

map : {l1 l2 l3}. [a b]. ((a -l1-> b) -l2-> List [a] -l3-> List [b])
    = {l1 l2 l3}. 
      \f @l2 xs @l3 .
        case xs {
	 Nil => Nil;
         Cons y ys => Cons (f y) (map {l1 l2 l3} f ys)
	};
	
	
main : List [Int] 
     = map {client server server}
         (\x @client . x + 5) (Cons 1 (Cons 2 (Cons 3 (Nil))))
	 