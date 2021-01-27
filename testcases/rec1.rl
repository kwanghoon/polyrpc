
// --------------------------------
// Testcase: Recursive functions
//   - location abstraction
//   - type abstraction
//   - value abstraction
// --------------------------------

f : {l}. [a]. ( a -l-> Int -l-> Int )
  = {l}. \x @ l  n @ l .
        if n <= 0 then 1
	else n * (f {l} x (n-1))

;

f_test : Int
  = f {client} 10 20

;

g : [a]. ( a -client-> Int -client-> Int )
  = \x @ client  n @ client.
        if n <= 0 then 1
	else n * (g x (n-1))

;

g_test : Int
  = g 10 20

;

h : Int -client-> Int -client-> Int
  = \x @ client  n @ client.
        if n <= 0 then 1
	else n * (h x (n-1))

;

h_test : Int
  = g 10 20




