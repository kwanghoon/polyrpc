
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Streams                                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

data Stream {l} a =  SNil | SCons a (Unit -> Stream {l} a)

;

// data Pair {l1 l2} a b = Pair (Ref {l1} a) (Ref {l2} b)

// Pair {l1 l2} : Ref {l1} a -> Ref {l2} b -> Pair {l1 l2} a b

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
   = SCons 1 (\unit @client.
      SCons 2 (\unit @client.
        SCons 3 (\unit @client. SNil)))
;

server_list1 : Stream {server} Int
   = SCons 1 (\unit @server.
      SCons 2 (\unit @server.
        SCons 3 (\unit @server. SNil)))

;

test1 : Int
     = hd_stream 
        (tl_stream 
	  (take_stream 
	    (map_stream
	       (\x@client. x+1) client_list1)
	    2))
	    
;

serverToclient
  : Stream {server} Int -> Stream {client} Int
  = \server_stream @ client .
      case server_stream {
        SNil => SNil;
	SCons y ys =>
	  SCons y
	    ( \unit @client. serverToclient (ys ()) )
      }
;

main : Stream {client} Int = serverToclient server_list1
