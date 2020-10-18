
x : Ref {server} [String] = ref {server} "one two three" ;

y : Unit = x := {server} "four five six" ;

z : Unit = print {client} ( ! {server} x )




