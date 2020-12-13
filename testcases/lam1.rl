
// ------------------------
// Testcase: Lambda - S,K,I
// ------------------------

i : {l}. [a]. (a -l-> a)
  = {l}. \x @ l . x;

k : {l}. [a b]. (a -l-> b -l-> a)
  = {l}. \x @ l  y @ l . x ;

s : {l1 l2 l3}. [a b c]. ( (a -l1-> b -l1-> c) -l3-> (a -l2-> b) -l3-> a -l3-> c)
  = {l1 l2 l3}. \f @ l3  g @ l3  x @ l3. f x (g x) 



