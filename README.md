# polyrpc

### A multi-tier functional programming language based on the polymorphic rpc calculus
 - Allow to write client, server, and location-polymorphic functions
 - A polyrpc programming language system including a parser, a poly rpc type checker, a slicing compiler, a poly cs type checker, and a poly cs interpter.
 - A bidirectional typechecking algorithm to infer many type annotations (not location ones) automatically
 
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
   - [A Polymorphic RPC calculus, Science of Computer Programming, Vol.197, Article 102499, October 2020.](https://www.sciencedirect.com/science/article/pii/S0167642320301088) [(arXiv)](https://arxiv.org/abs/1910.10988)
   - [A Theory of RPC calculi for Client-Server Model, Journal of Functional Programming, e5, 39, pages, 2019.](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/theory-of-rpc-calculi-for-clientserver-model/15DC9096F78E604ABD5F34A96F277EFE/share/48741a4dab3b936b9b47356fa95d481562050484)
   
 - A reference and its implementation extended with locations
   - [Jana Dunfield, Neelakantan R. Krishnaswami, Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism, ICFP2013](https://arxiv.org/abs/1306.6032)
   - [A simple extension with polymorphic locations](https://github.com/kwanghoon/bidi/tree/polyloc) based on [an implementation of the bidirectional type checking algorithm by [Olle Fredriksson](https://semantic-domain.blogspot.com/2013/04/thanks-to-olle-fredriksson.html).

 
### A web runtime system
 - [An experimental web runtime system in Scala by Bob Reynders](https://github.com/tzbob/rrpc)


