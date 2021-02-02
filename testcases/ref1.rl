
x1 : Ref {server} [String] = ref {server} "one two three" ;

data List = [a]. Nil | Cons a (List [a]) ;

x2 : Ref {server} [List [String]] = ref {server} Nil ;


y : Unit = x1 := {server} "four five six" ;

z : Unit = print {client} ( ! {server} x1 )





