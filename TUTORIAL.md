## PolyRPC: A multi-tier functional programming language for client-server model

### Main features
 - Locative functions, datatypes, and references


### A quick start to run helloworld.rl

~~~~
  $ git clone https://github.com/kwanghoon/genlrparser
  $ stack build
  $ cat ./app/polyrpc/examples/helloworld.rl
  
  main : Unit = print {client} "Hello World\n"

  $ stack exec -- polyrpc-exe ./app/polyrpc/examples/helloworld.rl
  
  Hello World
  $
~~~~

### Main features

#### Locative functions

- A client identity function 
~~~~
f : Int -client-> Int
  = \x @ client . x
~~~~

- A polymorphic identity function 
~~~~
id : {l}. [a]. (a -l-> a)
   = {l}. 
     \x @ l. x
~~~~

- A server identity function 
~~~~
g : Int-server-> Int
  = id {server}
~~~~


- A client factorial function
~~~~
fac : Int -client-> Int
    = \n @ client .
        if n <= 0 then 1
	else n * (fac (n-1))

;

main : Int = fac 3
~~~~

- A polymorphic map function: An example of running a server map function 
with the application of a client function to elements of a list
~~~~

data List = [a]. Nil | Cons a (List [a])  ;

map : {l1 l2}. [a b]. ((a -l1-> b) -l2-> List [a] -l2-> List [b])
    = {l1 l2}. 
      \f @l2 xs @l2 .
        case xs {
	 Nil => Nil;
         Cons y ys => Cons (f y) (map {l1 l2} f ys)
	};
	
	
main : List [Int] 
     = map {client server}
         (\x @client . x + 5) (Cons 1 (Cons 2 (Cons 3 (Nil))))
~~~~

#### Locative datatypes

- Locative streams: Stream {client} [Int] for client integer streams, Stream {server} [Int] for server integer streams

~~~~
data Stream = {l}. [a].  SNil | SCons a (Unit -l-> Stream {l} [a]) 

;

client_stream : Stream {client} [Int]
   = SCons {client} 1 (\unit @client.
      SCons {client} 2 (\unit @client.
        SCons {client} 3 (\unit @client. SNil {client} )))
;

server_stream : Stream {server} [Int]
   = SCons {server} 1 (\unit @server.
      SCons {server} 2 (\unit @server.
        SCons {server} 3 (\unit @server. SNil {server} )))
~~~~

- Locative stream functions

~~~~
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
~~~~

- Conversion of server streams into client streams

~~~~
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

main : Stream {client} [Int] = serverToclient server_stream1
~~~~

#### Locative references

- Create a server reference to "one two three" from the client, update it with "four five six", and then read the referenced string. 
~~~~
addr : Ref {server} [String] = ref {server} "one two three" ;

unit1 : Unit = addr := {server} "four five six" ;

unit2 : Unit = print {client} ( ! {server} addr )
~~~~


