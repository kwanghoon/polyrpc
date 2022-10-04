

// ------------------------
// Testcase: Case/Con/Tuple
// ------------------------


x1 : (Bool, Int, String) = (True, 123, "hello world") ;

x2 : ((Int, String), Bool) = ((012, "dear"), False) ;

x3 : ((Int, String), (Bool, Int)) = ((456, "winter"), (False, 789)) ;

x4 : String
   = case x1 {
       (b, i, s) => s
     } ;

x5 : Int
   = case x2 {
       (p1, b) =>
         case p1 {
	   (i, s) => i
	 }
     } ;

x6 : Int
   = case x3 {
       (p1, p2) =>
         case p1 {
           (i, s) =>
              case p2 {
                (b, j) => i+j   
              }
         }
     } 
	
	
