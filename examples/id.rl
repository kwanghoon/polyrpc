
id : {l}. forall a. (a -l-> a)
   = \x . x

;

test1 : Int = (\x . x) 123

;

test2 : Int -server-> Int = \server: z. (\x . x) 123

;

test3 : Int = (\z. (\x . x) 123) 456

;

aux4 : server: (Int -> Int) -> Int = \z. z 123

;

test4 : Int = aux4 (\x . x)







