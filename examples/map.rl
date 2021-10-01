
data List a = Nil | Cons a (List a)  ;

map : forall a b.  (a -> b) -> List a -> List b
    = \f xs .
        case xs {
	 Nil => Nil;
         Cons y ys => Cons (f y) (map f ys)
	};
	
	
main : List Int
     = map 
         (\client: x . x + 5) (Cons 1 (Cons 2 (Cons 3 (Nil))))
	 