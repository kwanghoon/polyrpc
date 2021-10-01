
x : Int
  = let {

      id : [a]. a -client-> a
         = \x @ client. x
    }
      let {

        y : Int = id 3

      } y
      end
      
    end ;


z : Int
  = let {

      id : {l}. [a]. a -l-> a
         = {l}. \x @ l. x
    }
      let {

        w : {l}. [b]. b -l-> b
	  = {l}. \z @ l.
	      let {
	        r : Ref {l} [b] = ref {l} z
	      } id {l} z
	      end

      } w {client} 3
      end
      
    end 

