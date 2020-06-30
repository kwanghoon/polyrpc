
x : Int
  = let {

      id : [a]. a -client-> a
         = [a]. \x : a @ client. x
    }
      let {

        y : Int = id [Int] 3

      } y
      end
      
    end ;


z : Int
  = let {

      id : {l}. [a]. a -l-> a
         = {l}. [a]. \x : a @ l. x
    }
      let {

        w : {l}. [b]. b -l-> b
	  = {l}. [b]. \z : b @ l.
	      let {
	        r : Ref {l} [b] = ref {l} [b] z
	      } id {l} [b] z
	      end

      } w {client} [Int] 3
      end
      
    end 

