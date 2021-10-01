
///////////////////////////////////////
// Location annotations in datatypes //
///////////////////////////////////////

// (Case 1)
//    The location in Stream {l} a is the same as that on (... -> ...)

data Stream {l} a =  SNil | SCons a (Unit -l-> Stream {l} a); 

data StreamWrong {l l0} a =  SNilWrong | SConsWrong a (Unit -l0-> Stream {l} a); 

// (Case 2)
//    The location in Stream {l} a is different from that on (... -> ...)

data Strange {l l1 l2} a b =  Strange (Pair {l1 l2} a b -l-> Unit);

// (Case 3)
//    Locations appear on in applications, not on (... -> ...)
data Pair {l1 l2} a b = Pair (Ref {l1} a) (Ref {l2} b);


// (Case 4)
//    Locations do not appear at all but a location variable is introduced 
//    since there are one or more function types.
data Plain {l} = Plain (Unit -l-> Unit);

data Plain2 {l} = Plain2 (Unit -l-> Unit) (Unit -l-> Unit); 

// (Case 5)
//    No locations are involved.
data List a = Nil | Cons a (List a)


