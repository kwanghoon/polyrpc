# Polyrpc

### A multi-tier functional programming language based on the polymorphic rpc calculus
 - Allow to write client, server, and location-polymorphic functions
 - A polyrpc programming language system including a parser, a poly rpc type checker, a slicing compiler, a poly cs type checker, and a poly cs interpter.
 - A polymorphic location inference algorithm based on bidirectional typechecking.
 - Syntactic sugar for location annotations (particularly for location-independent functions)

### News
 - A bidirectional location inference algorithm is available in the master branch. Examples are available at examples.
 - Use --debug-parse to see a desugared term before the inference and --dump-typecheck to check a location inferenced term
 - For experts, --debug-typecheck is available to see how the bidirectional inference is working in detail. 
 
 
### Download and build
~~~
  $ git clone https://github.com/kwanghoon/polyrpc
  $ cd polyrpc
  $ stack build
~~~ 

### Run an polyrpc interpreter
~~~
$ stack exec -- polyrpc ./examples/helloworld.rl
POLYRPC, version 0.1.0: http://github.com/kwanghoon/polyrpc/
[Reading] ./examples/helloworld.rl
[Lexing]
[Parsing]
[Type checking]
[Compiling]
[Verifying generated codes]
[Executing codes]
Hello World
[Success]
~~~

### Documents
 - [Tutorial](TUTORIAL.md)
 - Research papers
   - [A Typed Slicing Compilation for the Polymorphic RPC Calculus, the 23rd International Symposium on Principles and Practice of Declarative Programming (PPDP), September 2021. (arXiv)](https://arxiv.org/abs/2107.10793)
   - [A Polymorphic RPC calculus, Science of Computer Programming, Vol.197, Article 102499, October 2020.](https://www.sciencedirect.com/science/article/pii/S0167642320301088) [(arXiv)](https://arxiv.org/abs/1910.10988)
   - [A Theory of RPC calculi for Client-Server Model, Journal of Functional Programming, e5, 39, pages, 2019.](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/theory-of-rpc-calculi-for-clientserver-model/15DC9096F78E604ABD5F34A96F277EFE/share/48741a4dab3b936b9b47356fa95d481562050484)
   
 - A polymorphic location inference algorithm based on bidirectional type checking 
   - The surface syntax is available in surface/Surface.hs.
   - Based on [Jana Dunfield, Neelakantan R. Krishnaswami, Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism, ICFP2013](https://arxiv.org/abs/1306.6032)
     and [its implementation of the bidirectional type checking algorithm by Olle Fredriksson](https://semantic-domain.blogspot.com/2013/04/thanks-to-olle-fredriksson.html).
   - The algorithm is for the predicative subset of the polymorphic RPC calculus.

 
### Web runtime systems for PolyRPC
 - [A web runtime system in Haskell](https://github.com/kwanghoon/todomvc)
 - [An experimental web runtime system in Scala by Bob Reynders](https://github.com/tzbob/rrpc)


