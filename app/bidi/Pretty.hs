{-# LANGUAGE GADTs #-}
-- | Pretty printing
module Pretty where

import Naming
import Location
import Type
import Context
-- import AST

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

instance Pretty Location where
  bpretty _ (Location locstr) = showString locstr
  bpretty d (LocVar lvar)
    | clExists lvar = showString "∃ " . bpretty d lvar
    | otherwise     = bpretty d lvar

instance Pretty Type where
  bpretty d typ = case typ of
    TypeVarType v ->
      if cExists v
      then showParen (d > exists_prec) $
           showString "∃ " . bpretty exists_prec v
      else bpretty d v
    TupleType tys ->
      showString "(" . showTuple tys . showString ")"
    FunType t1 loc t2 -> showParen (d > fun_prec) $
      bpretty (fun_prec + 1) t1 .
      showString " -" . bpretty d loc  . showString "-> " .
      bpretty fun_prec t2
    TypeAbsType vs t -> showParen (d > forall_prec) $
      showString "∀ " . bpretty (forall_prec + 1) vs .
      showString ". "      . bpretty forall_prec t
    LocAbsType ls t -> showParen (d > forall_prec) $
      showString "∀ " . bpretty (forall_prec + 1) ls .
      showString ". "      . bpretty forall_prec t
    ConType c ls tys ->
      showString c. showSpace (null ls) (showLocs ls). showTys tys
    where
      exists_prec = 10
      forall_prec :: Int
      forall_prec = 1
      fun_prec    = 1

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

instance Pretty (GContext a) where
  bpretty d (Context xs) = bpretty d $ reverse xs

instance Pretty (ContextElem a) where
  bpretty d cxte = case cxte of
    CForall v  -> bpretty d v
    CVar v t -> showParen (d > hastype_prec) $
      bpretty (hastype_prec + 1) v . showString " : " . bpretty hastype_prec t
    CExists v -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec v
    CExistsSolved v t -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec v .
      showString " = " . bpretty exists_prec t
    CMarker v -> showParen (d > app_prec) $
      showString "▶ " . bpretty (app_prec + 1) v

    CLForall l -> bpretty d l
    CLExists l -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec l
    CLExistsSolved l loc -> showParen (d > exists_prec) $
      showString "∃ " . bpretty exists_prec l .
      showString " = " . bpretty exists_prec loc
    CLMarker l -> showParen (d > app_prec) $
      showString "▶ " . bpretty (app_prec + 1) l

    where
      exists_prec = 1
      hastype_prec = 1
      app_prec     = 10
