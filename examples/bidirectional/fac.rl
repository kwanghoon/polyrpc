
fac : Int -client-> Int
    = \n @ client .
        if n <= 0 then 1
	else n * (fac (n-1))

;

main : Int = fac 3

