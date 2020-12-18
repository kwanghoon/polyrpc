
// --------------------------------
// Testcase: Nested let expressions
// --------------------------------

x1 : Bool = True ;

x2 : String
   = let { x1 : String = "hello world" } x1 end ;

x3 : Bool
   = let { x : Bool = True } x end ;

x4 : Int
   = let {
        id : {l}. [a]. a -l-> a = {l}. \x @ l. x ;
	x : Int = 123
     } id {server} x end ;

x5 : Int
   = let {
        id : {l}. [a]. a -l-> a = {l}. \x @ l. x ;
	
	x : Int =
	   let {
	      y : Int = 456
	   } id {server} y end
	   
     } x end ;


x6 : (String, Bool, Int)
   = (x2, x3, x4) ;

x7 : Bool
   = let {
       x : Int = 789
     } let {
        x : Bool = False
       } x end
     end

