
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Streams                                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

data Stream = {l}. [a].  Nil | Cons a (Unit -l-> Stream {l} [a]) 

;

hd_stream
   : {l1 l2}. [a]. (Stream {l1} [a] -l2-> a)
   = {l1 l2}. \s @ l2 .
      case s {
        Cons x xs => x
      }

;

tl_stream
   : {l1 l2}. [a]. (Stream {l1} [a] -l2-> Stream {l1} [a])
   = {l1 l2}. \s @ l2 .
      case s {
        Cons x xs => xs ()
      }
      
;

map_stream
    : {l1 l2 l3 l4}. [a b]. ((a -l2-> b) -l3-> Stream {l1} [a] -l4-> Stream {l1} [b])
    = {l1 l2 l3 l4}.
      \f @l3 xs @l4 .
        case xs {
	 Nil => Nil {l1};
         Cons y ys => Cons {l1} (f y) (\unit @ l1 . map_stream {l1 l2 l3 l4} f (ys ()) )
	}

;

take_stream
    : {l1 l2 l3}. [a]. (Stream {l1} [a] -l2-> Int -l3-> Stream {l1} [a])
    = {l1 l2 l3}.
      \s @ l2
       n @ l3 .
        case s {
	  Nil => Nil {l1};
	  Cons y ys =>
	    if n <= 0
	    then Nil {l1}
	    else Cons {l1} y (\unit @ l1 . take_stream {l1 l2 l3} (ys ()) (n-1))
	}
;

////////////////////////////////////////////////////////////////////////////////
// main
////////////////////////////////////////////////////////////////////////////////

client_list1 : Stream {client} [Int]
   = Cons {client} 1 (\unit @client.
      Cons {client} 2 (\unit @client.
        Cons {client} 3 (\unit @client. Nil {client})))
;

server_list1 : Stream {server} [Int]
   = Cons {server} 1 (\unit @server.
      Cons {server} 2 (\unit @server.
        Cons {server} 3 (\unit @server. Nil {server})))

;

test1 : Int
     = hd_stream {client client}
        (tl_stream {client client} 
	  (take_stream {client client client} 
	    (map_stream {client client client client}
	       (\x@client.x+1) client_list1)
	    2))
;

serverToclient
  : Stream {server} [Int] -client-> Stream {client} [Int]
  = \server_stream @ client .
      case server_stream {
        Nil => Nil {client};
	Cons y ys =>
	  Cons {client} y
	    ( \unit@client. serverToclient (ys ()) )
      }
;

main : Stream {client} [Int] = serverToclient server_list1
