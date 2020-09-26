
f : Int -client-> Int
  = \x : Int @ client . x

;


// Infinite loop in the simplifcation
main : Unit = print {client} (intToString {client} (f 42))

// main : Unit = let { z : Int = f 42 } () end
