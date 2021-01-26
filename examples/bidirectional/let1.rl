test : [a]. a -client-> Unit
= \x @ client. let { ignore: Unit = test x } () end

// ;

// main : Unit = test 123
