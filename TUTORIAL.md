## PolyRPC: A multi-tier functional programming language for client-server model

### Main features
 - Locative functions, datatypes, and references


### A quick start to run helloworld.rl

~~~~
  $ git clone https://github.com/kwanghoon/polyrpc
  $ cd polyrpc
  $ stack build
  $ cat ./examples/helloworld.rl
  
  main : Unit = print "Hello World\n"

  $ stack exec -- polyrpc-exe ./examples/helloworld.rl
  Hello World
  $
~~~~

### Main features

#### Locative functions

- A client identity function 
~~~~
f : Int -client-> Int
  = \x . x
~~~~

- A polymorphic identity function 
~~~~
id : forall a. a -> a
   = \x. x
~~~~

- A server identity function 
~~~~
g : Int-server-> Int
  = id 
~~~~


- A client factorial function
~~~~
fac : Int -client-> Int
    = \n. if n <= 0 then 1 else n * (fac (n-1))
;
main : Int = fac 3
~~~~

- A polymorphic map function: An example of running a polymorphic map function 
with the application of a client function to elements of a list
~~~~

data List a = Nil | Cons a (List a)  ;

map : forall a b. (a -> b) -> List a -> List b
    = \f xs .  case xs {
        Nil => Nil;
         Cons y ys => Cons (f y) (map f ys)
	};
	
	
main : List Int
     = map (\client: x. x + 5) (Cons 1 (Cons 2 (Cons 3 (Nil))))
~~~~

#### Locative datatypes

- Locative streams: Stream {client} Int for client integer streams, Stream {server} Int for server integer streams

~~~~
data Stream {l} a = SNil | SCons a (Unit -l-> Stream {l} a) 

;

client_stream : Stream {client} Int
   = SCons 1 (\unit.
      SCons 2 (\unit.
        SCons 3 (\unit. SNil)))
;

server_stream : Stream {server} Int
   = SCons 1 (\unit.
      SCons 2 (\unit.
        SCons 3 (\unit. SNil)))
~~~~

- Locative stream functions

~~~~
hd_stream
   : {l1 l2}. forall a. Stream {l1} a -l2-> a
   = \s.
      case s {
        SCons x xs => x
      }

;

tl_stream
   : {l1 l2}. forall a. Stream {l1} a -l2-> Stream {l1} a
   = \s .
      case s {
        SCons x xs => xs ()
      }
      
;

map_stream
    : {l1 l2}. forall a b. l2: (a -> b) -> Stream {l1} a -> Stream {l1} b
    = \f xs.
        case xs {
	 SNil => SNil;
         SCons y ys => SCons (f y) (\unit. map_stream f (ys ()) )
	}

;

take_stream
    : {l1 l2}. forall a. l2: Stream {l1} a -> Int -> Stream {l1} a
    = \s n .
        case s {
         SNil => SNil {l1};
         SCons y ys =>
           if n <= 0
           then SNil
           else SCons y (\unit. take_stream (ys ()) (n-1))
	}
~~~~

- Conversion of server streams into client streams

~~~~
serverToclient
  : Stream {server} [Int] -client-> Stream {client} [Int]
  = \client: server_stream .
      case server_stream {
        SNil => SNil;
        SCons y ys =>
          SCons y ( \client: unit. serverToclient (ys ()) )
      }
;

main : Stream {client} Int = serverToclient server_stream1
~~~~

#### Locative references

- Create a server reference to "one two three" from the client, update it with "four five six", and then read the referenced string. 
~~~~
addr : Ref {server} String = ref "one two three" ;

unit1 : Unit = addr := "four five six" ;

unit2 : Unit = print ( ! addr )
~~~~


