
// K = \x y. x
//
//    -  {l}. forall a b. a -l-> b -l-> a
//    -  {l1 l2}. forall a b. a -l1-> b -l2-> a

k_one : forall a b. a -> b -> a
  = \x y. x  
;

k_two : {l1 l2}. forall a b. a -l1-> b -l2-> a
  = \x y. x  

;

k_three : {l1} . forall a . a -l1-> ({l2}. forall b. b -l2-> a)
  = \x y. x  

;

// S = \f g x. f x (g x)

s_one : forall a b c. (a -> b -> c) -> (a -> b) -> a -> c
  = \f g x. f x (g x)

;

s_two : forall a b c. client: (a -> b -> c) -> (a -> b) -> a -> c
  = \f g x. f x (g x)

;

s_three : {l1 l2 l3}. forall a b c. l1: (l2: a -> b -> c) -> (l3: a -> b) -> a -> c
  = \f g x. f x (g x)

;

s_four : {l11 l12 l13 l21 l22 l31}. forall a b c. (a -l21-> b -l22-> c) -l11-> (a -l31-> b) -l12-> a -l13-> c
  = \f g x. f x (g x)



