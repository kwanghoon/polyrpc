
///////////////////////////////////////
// Location annotations in datatypes //
///////////////////////////////////////

// (Case 1)
//    The location in Stream {l} a is the same as that on (... -> ...)

data Stream {l} a =  SNil | SCons a ({l} Unit -> Stream {l} a); // Todo:  good or bad?

// (Case 2)
//    The location in Stream {l} a is different from that on (... -> ...)

data Strange {l l1 l2} a b =  Strange ({l} Pair {l1 l2} a b -> Unit);  // Todo: good or bad?

// (Case 3)
//    Locations appear on in applications, not on (... -> ...)
data Pair {l1 l2} a b = Pair (Ref {l1} a) (Ref {l2} b);


// (Case 4)
//    Locations do not appear at all but a location variable is introduced 
//    since there is a function type.
data Plain {l} = Plain ({l} Unit -> Unit); // data Plain {l} = Plain (Unit -l-> Unit)

// (Case 5)
//    No locations are involved.
data List a = Nil | Cons a (List a)

////////////////////////////////////////////////////////////////
// Location annotations in types for expressions/declarations //
////////////////////////////////////////////////////////////////

// Locations are allowed only in applications. Any location 
// annotations on function types are not allowed in types 
// but they are annotated to terms, i.e., lambda abstractions.

