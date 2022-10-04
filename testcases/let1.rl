
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
     end;

x8 : Int
   = let {
        z : Int = 135 ;
	y : Int
	  = let {
	       w : Int = z
	    } w end
     } y end ;

x9 : Int
   = let {
        a : Int = 135 ;
        b : Int = 135 ;
        c : Int = 135 ;
        z : Int = 135 ;
	y : Int
	  = let {
	       w : Int = z
	    } w end
     } y end ;

x10 : Int
   = let {
        z : Int = 135 ;
        a : Int = 135 ;
        b : Int = 135 ;
        c : Int = 135 ;
	y : Int
	  = let {
	       w : Int = z
	    } w end
     } y end ;

x11 : Int
   = let {
        a : Int = 135 ;
        b : Int = 135 ;
        z : Int = 135 ;
        c : Int = 135 ;
	y : Int
	  = let {
	       w : Int = z
	    } w end
     } y end ;

x12 : Int
   = let {
        a : Int = 135 ;
        b : Int = 135 ;
        z : Int = 135 ;
        c : Int = 135 ;
	y : Int
	  = let {
               d : Int = 135 ;
	       w : Int = z
	    } w end
     } y end ;


x13 : String
   = let {
       z : String = "hello world" ;
       w : String = z
     } w end ;


x14 : String
   = let {
        z : Bool = True ;
	y : String
	  = let {
               z : String = "helloworld" ;
	       w : String = z
	    } w end
     } y end 



