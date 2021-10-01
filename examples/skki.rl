// -----------------
// S,K,I combinators
// -----------------

s : forall a b c. (a -> b -> c) -> (a -> b) -> a -> c
  = \f  g  x. f x (g x) ;

k : forall a b. (a -> b -> a)
  = \x  y. x ;


identity
  : forall a. (a -> a)
  = \x. s k k x

;

main : Int
  = identity 123

// main : Unit
//   = print {client} (intToString {client} (identity {client} 123))

