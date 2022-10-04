
x1 : Ref {server} String = ref "one two three" ;

data List a = Nil | Cons a (List a) ;

x2 : Ref {server} (List String) = ref Nil ;


y : Unit = x1 := "four five six" ;

z : Unit = print ( ! x1 )





