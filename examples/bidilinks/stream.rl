
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Streams                                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

data Stream {l} a =  SNil | SCons a ({l} Unit -> Stream {l} a) // Todo:  good or bad?

;

// data Pair {l1 l2} a b = Pair (Ref {l1} a) (Ref {l2} b)

// data Strange {l l1 l2} a b =  Strange ({l} Pair {l l1 l2} a b -> Unit)  // Todo: good or bad?

// ;

hd_stream
   : forall a. Stream {l} a -> a
   = \s.
      case s {
        SCons x xs => x
      }

;

tl_stream
   : forall a. Stream {l} a -> Stream {l} a
   = \s.
      case s {
        SCons x xs => xs ()
      }
      
;

map_stream
   : forall a b. (a -> b) -> Stream {l} a -> Stream {l} b
   = \f xs.
        case xs {
	 SNil => SNil;
         SCons y ys => SCons (f y) (\unit. map_stream f (ys ()) )
	}

;

take_stream
    : forall a. Stream {l} a -> Int -> Stream {l} a
    = \s n.
        case s {
	  SNil => SNil;
	  SCons y ys =>
	    if n <= 0
	    then SNil
	    else SCons y (\unit. take_stream (ys ()) (n-1))
	}
;

////////////////////////////////////////////////////////////////////////////////
// main
////////////////////////////////////////////////////////////////////////////////

client_list1 : Stream {client} Int
   = SCons 1 (\{client} unit.
      SCons 2 (\{client} unit.
        SCons 3 (\{client} unit. SNil)))
;

server_list1 : Stream {server} Int
   = SCons 1 (\{server} unit.
      SCons 2 (\{server} unit.
        SCons 3 (\{server} unit. SNil)))

;

test1 : Int
     = hd_stream 
        (tl_stream 
	  (take_stream 
	    (map_stream
	       (\{client} x. x+1) client_list1)
	    2))
	    
;

serverToclient
  : Stream {server} Int -> Stream {client} Int
  = \{client} server_stream .
      case server_stream {
        SNil => SNil;
	SCons y ys =>
	  SCons y
	    ( \{client} unit. serverToclient (ys ()) )
      }
;

main : Stream {client} Int = serverToclient server_list1
