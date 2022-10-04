// ---------------------------
// S,K,I combinators (Complex)
// ---------------------------

s : {l11 l12 l2 l31 l32 l33}. [a b c]. ( (a -l11-> b -l12-> c) -l31-> (a -l2-> b) -l32-> a -l33-> c)
  = {l11 l12 l2 l31 l32 l33}. \f @ l31  g @ l32  x @ l33. f x (g x) ;

k : {l1 l2}. [a b]. (a -l1-> b -l2-> a)
  = {l1 l2}. \x @ l1  y @ l2 . x ;

// i : {l}. [a]. (a -l-> a)
//   = {l}. \x @ l . x ;


identity
  : {l}. [a]. (a -l-> a)
  = {l}. \x @ l. s {l l l l l l} (k {l l}) (k {l l}) x

;

main : Int
  = identity {client} 123

// main : Unit
//   = print {client} (intToString {client} (identity {client} 123))
