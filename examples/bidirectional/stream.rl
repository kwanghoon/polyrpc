
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Streams                                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

data Stream = {l}. [a].  SNil | SCons a (Unit -l-> Stream {l} [a]) 

;

hd_stream
   : {l1 l2}. [a]. (Stream {l1} [a] -l2-> a)
   = {l1 l2}. \s @ l2 .
      case s {
        SCons x xs => x
      }

;

tl_stream
   : {l1 l2}. [a]. (Stream {l1} [a] -l2-> Stream {l1} [a])
   = {l1 l2}. \s @ l2 .
      case s {
        SCons x xs => xs ()
      }
      
;

map_stream
    : {l1 l2 l3}. [a b]. ((a -l2-> b) -l3-> Stream {l1} [a] -l3-> Stream {l1} [b])
    = {l1 l2 l3}.
      \f @l3 xs @l3 .
        case xs {
	 SNil => SNil {l1};
         SCons y ys => SCons {l1} (f y) (\unit @ l1 . map_stream {l1 l2 l3} f (ys ()) )
	}


;

take_stream
    : {l1 l2}. [a]. (Stream {l1} [a] -l2-> Int -l2-> Stream {l1} [a])
    = {l1 l2}.
      \s @ l2
       n @ l2 .
        case s {
	  SNil => SNil {l1};
	  SCons y ys =>
	    if n <= 0
	    then SNil {l1}
	    else SCons {l1} y (\unit @ l1 . take_stream {l1 l2} (ys ()) (n-1))
	}
;

////////////////////////////////////////////////////////////////////////////////
// main
////////////////////////////////////////////////////////////////////////////////

client_list1 : Stream {client} [Int]
   = SCons {client} 1 (\unit @client.
      SCons {client} 2 (\unit @client.
        SCons {client} 3 (\unit @client. SNil {client})))
;

server_list1 : Stream {server} [Int]
   = SCons {server} 1 (\unit @server.
      SCons {server} 2 (\unit @server.
        SCons {server} 3 (\unit @server. SNil {server})))

;

test1 : Int
     = hd_stream {client client}
        (tl_stream {client client}
	  (take_stream {client client}
	    (map_stream {client client client}
	       (\x@client.x+1) client_list1)
	    2))
	    
;

serverToclient
  : Stream {server} [Int] -client-> Stream {client} [Int]
  = \server_stream @ client .
      case server_stream {
        SNil => SNil {client};
	SCons y ys =>
	  SCons {client} y
	    ( \unit @client. serverToclient (ys ()) )
      }
;

main : Stream {client} [Int] = serverToclient server_list1
