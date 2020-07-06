// mkClosure: free variable not found

f : Int -client-> Int -client-> Int
  = \x:Int @ client y:Int @ client.
    case (x, y) {
      (r, i) => (\z:Int @ client . r) 0
    }

