// -----------------
// S,K,I combinators
// -----------------

s : [a b c]. ( (a -client-> b -client-> c) -client-> (a -client-> b) -client-> a -client-> c)
  = \f @ client  g @ client  x @ client. f x (g x) ;

k : [a b]. (a -client-> b -client-> a)
  = \x @ client  y @ client . x ;

// i : [a]. (a -client-> a)
//   = \x @ client . x ;


identity
  : [a]. (a -client-> a)
  = \x @ client. s k k x

;

main : Int
  = identity 123

// main : Unit
//   = print {client} (intToString {client} (identity 123))
