
data Pair = [a]. Pair a a ;

id : {l}. [a]. (a -l-> a)
   = {l}.
     \x @ l. x;

x : Int = id {client} 1;

main : Pair [Int] = id {client} (Pair 1 2)
