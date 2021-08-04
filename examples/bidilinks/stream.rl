
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Streams                                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

data Stream {l} a =  SNil | SCons a (Unit -l-> Stream {l} a)

;

hd_stream
   : {l}. forall a. Stream {l} a -l-> a
   = \s.
      case s {
        SCons x xs => x
      }

;

tl_stream
   : {l}. forall a. Stream {l} a -l-> Stream {l} a
   = \s.
      case s {
        SCons x xs => xs ()
      }
      
;

map_stream
   : {l}. forall a b. l: (a -> b) -> Stream {l} a -> Stream {l} b
   = \f xs.
        case xs {
	 SNil => SNil;
         SCons y ys => SCons (f y) (\unit. map_stream f (ys ()) )
	}

;

take_stream
    : {l}. forall a. l: Stream {l} a -> Int -> Stream {l} a
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
   = SCons 1 (\unit.                    // Todo: lifted to a {l}. \{l} unit. ...
      SCons 2 (\unit.                   // but can be optimized to \{client} unit. ...
        SCons 3 (\unit. SNil)))         // by compiler!
;

server_list1 : Stream {server} Int
   = SCons 1 (\unit.
      SCons 2 (\unit.
        SCons 3 (\unit. SNil)))

;

test1 : Int
     = hd_stream 
        (tl_stream 
	  (take_stream 
	    (map_stream
	       (\client: x. x+1) client_list1)
	    2))
	    
;

serverToclient
  : Stream {server} Int -client-> Stream {client} Int
  = \client: server_stream .
      case server_stream {
        SNil => SNil;
	SCons y ys =>
	  SCons y
	    ( \client: unit. serverToclient (ys ()) )  // Todo: Can {client} be omitted?
      }
;

main : Stream {client} Int = serverToclient server_list1
