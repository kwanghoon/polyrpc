{-# LANGUAGE GADTs #-}
-- | Pretty printing
module Pretty where

pretty :: Pretty a => a -> String
pretty x = bpretty 0 x ""

class Pretty a where
  bpretty :: Int -> a -> ShowS

instance Pretty a => Pretty (Maybe a) where
  bpretty d Nothing  = showString ""
  bpretty d (Just x) = bpretty d x

instance Pretty a => Pretty [a] where
  bpretty _ list = showString "[" . go list
    where
      go []     = showString "]"
      go [x]    = bpretty 0 x . go []
      go (x:xs) = bpretty 0 x . showString ", " . go xs

instance (Pretty a, Pretty b) => Pretty (a, b) where
  bpretty _ (x, y) =
    showString "("  . bpretty 0 x .
    showString ", " . bpretty 0 y .
    showString ")"

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  bpretty _ (x, y, z) =
    showString "("  . bpretty 0 x .
    showString ", " . bpretty 0 y .
    showString ", " . bpretty 0 z .
    showString ")"

instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
  bpretty _ (w, x, y, z) =
    showString "("  . bpretty 0 w .
    showString ", " . bpretty 0 x .
    showString ", " . bpretty 0 y .
    showString ", " . bpretty 0 z .
    showString ")"

instance Pretty Char where
  bpretty _ ch = showString [ch]

instance (Pretty a, Pretty b) => Pretty (a -> b) where
  bpretty _ f = showString "(...->...)"

{-
instance Pretty Var where
  bpretty _ (Var v) = showString v

instance Pretty TVar where
  bpretty _ (TypeVar v) = showString v

instance Pretty LVar where
  bpretty _ (LocVar v) = showString v
-}

showVars [] = \x -> x
showVars xs = showTuple_ "" xs 

showTyVars [] = \x -> x
showTyVars xs = showString "[" . showTuple_ "" xs . showString "]"

showLocVars [] = \x -> x
showLocVars xs = showString "{" . showTuple_ "" xs . showString "}"

showVarMaybeTyLocs [] = \x -> x
showVarMaybeTyLocs [(x,maybeTy,loc)] =
  showString x . showString ":" . bpretty 0 maybeTy . showString "@" . bpretty 0 loc
showVarMaybeTyLocs ((x,maybeTy,loc):xmls) =
  showString x . showString ":" . bpretty 0 maybeTy .showString "@" . bpretty 0 loc . showString " " .
  showVarMaybeTyLocs xmls

showLocs [] = \x -> x
showLocs xs = showString "{" . showTuple_ "," xs . showString "}"

showTys [] = \x -> x
showTys xs = showString "[" . showTuple_ "," xs . showString "]"

showTuple xs = showString "(" . showTuple_ "," xs . showString ")"

showTuple_ deli []     = showString ""
showTuple_ deli [x]    = bpretty 0 x
showTuple_ deli (x:xs) = bpretty 0 x . showString deli . showTuple_ deli xs

showSpace True f  = showString " " . f . showString " "
showSpace False f = f

showWith del [] = showString ""
showWith del [x] = showString x
showWith del (x:xs) = showString x . showString del . showWithComma xs

showWithComma xs = showWith "," xs

showWithSpace xs = showWith " " xs
