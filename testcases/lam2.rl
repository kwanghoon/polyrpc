
// ---------------------
// Testcase: higher-rank
// ---------------------

poly
   : {l1 l2}. ( ({l}. [a]. a -l-> a) -l2-> (Int, String) )
   = {l1 l2}. \id @ l2. (id {l1} 123, id {l2} "123") ;

main
   : (Int, String)
   = poly {client server} ({l}. \x @ l. x)
