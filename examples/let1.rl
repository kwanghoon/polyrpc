test : [a]. a -client-> Unit
= [a]. \x: a @ client. let { ignore: Unit = test [a] x } () end
