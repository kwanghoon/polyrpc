
// ------------------------
// Testcase: Lambda - S,K,I
// ------------------------

s : {l1 l2 l3}. [a b c]. ( (a -l1-> b -l1-> c) -l3-> (a -l2-> b) -l3-> a -l3-> c)
  = {l1 l2 l3}. \f @ l3  g @ l3  x @ l3. f x (g x) ;

k : {l}. [a b]. (a -l-> b -l-> a)
  = {l}. \x @ l  y @ l . x ;

i : {l}. [a]. (a -l-> a)
  = {l}. \x @ l . x ;


identity
  : {l}. [a]. (a -l-> a)
  = {l}. \x @ l. s {l l l} (k {l}) (k {l}) x






