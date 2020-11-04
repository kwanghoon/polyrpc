{-# LANGUAGE GADTs #-}
-- | Pretty printing
module Pretty where

pretty :: Pretty a => a -> String
pretty x = bpretty 0 x ""

class Pretty a where
  bpretty :: Int -> a -> ShowS

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

{-
instance Pretty Var where
  bpretty _ (Var v) = showString v

instance Pretty TVar where
  bpretty _ (TypeVar v) = showString v

instance Pretty LVar where
  bpretty _ (LocVar v) = showString v
-}

showLocs [] = \x -> x
showLocs xs = showString "{" . showTuple_ xs . showString "}"

showTys [] = \x -> x
showTys xs = showString "[" . showTuple_ xs . showString "]"

showTuple xs = showString "(" . showTuple_ xs . showString ")"

showTuple_ []     = showString ""
showTuple_ [x]    = bpretty 0 x
showTuple_ (x:xs) = bpretty 0 x . showString "," . showTuple_ xs

showSpace True f  = showString " " . f . showString " "
showSpace False f = f

-- instance Pretty Expr where
--   bpretty d expr = case expr of
--     EVar v       -> bpretty d v
--     EUnit        -> showString "()"
--     EAbs v loc e -> showParen (d > abs_prec) $
--       showString "λ" . bpretty (abs_prec + 1) v .
--       showString " @ " . bpretty (abs_prec + 1) loc .
--       showString ". " . bpretty abs_prec e
--     ELocAbs l e -> showParen (d > abs_prec) $
--       showString "Λ" . bpretty (abs_prec + 1) l .
--       showString ". " . bpretty abs_prec e
--     EApp e1 e2   -> showParen (d > app_prec) $
--       bpretty app_prec e1 . showString " " . bpretty (app_prec + 1) e2
--     ELocApp e loc   -> showParen (d > app_prec) $
--       bpretty app_prec e . showString " " . bpretty (app_prec + 1) loc
--     EAnno e t -> showParen (d > anno_prec) $
--       bpretty (anno_prec + 1) e . showString " : " . bpretty anno_prec t
--     where
--       abs_prec  = 1
--       app_prec  = 10
--       anno_prec = 1

