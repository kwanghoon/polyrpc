test : [a]. a -client-> Unit
= \x @ client. let { ignore: Unit = test x } () end
