{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Erase where

import Location
import qualified CSExpr as TE -- (Typed) Target expressions
import qualified UntypedCSExpr as UE  -- Untyped target expressions

---------------------------------------------
-- Erase types and locations from expressions
---------------------------------------------
erase :: TE.Expr -> IO UE.Expr
erase (TE.ValExpr v) = do
  uv <- eraseVal v
  return (UE.ValExpr uv)

erase (TE.Let bindingDecls expr) = do
  untyped_bindingDecls <- mapM eraseBindingDecl bindingDecls
  untyped_expr <- erase expr
  return (UE.Let untyped_bindingDecls untyped_expr)

erase (TE.Case val ty alts) = do
  untyped_val <- eraseVal val
  untyped_alts <- mapM eraseAlt alts
  return (UE.Case untyped_val untyped_alts)

erase (TE.App fn ty arg) = do
  untyped_fn <- eraseVal fn
  untyped_arg <- eraseVal arg
  return (UE.App untyped_fn untyped_arg)

erase (TE.TypeApp fn ty argtys) = do
  untyped_fn <- eraseVal fn
  return $ UE.ValExpr untyped_fn

erase (TE.LocApp fn ty arglocs) = do
  untyped_fn <- eraseVal fn
  return $ UE.ValExpr untyped_fn

erase (TE.Prim primOp locs tys vals) = do
  locVals <- mapM locationToValue locs
  untyped_vals <- mapM eraseVal vals
  return (UE.Prim primOp locVals untyped_vals)

--
eraseBindingDecl (TE.Binding x ty expr) = do
  untyped_expr <- erase expr
  return (UE.Binding x untyped_expr)

--
eraseAlt (TE.Alternative conname xs expr) = do
  untyped_expr <- erase expr
  return (UE.Alternative conname xs untyped_expr)

eraseAlt (TE.TupleAlternative xs expr) = do
  untyped_expr <- erase expr
  return (UE.TupleAlternative xs untyped_expr)
  

----------------------------------------
-- Erase types and locations from values
----------------------------------------
eraseVal :: TE.Value -> IO UE.Value
eraseVal (TE.Var x) = return (UE.Var x)
eraseVal (TE.Lit lit) = return (UE.Lit lit)
eraseVal (TE.Tuple vals) = do
  untyped_vals <- mapM eraseVal vals
  return (UE.Tuple untyped_vals)
eraseVal (TE.Constr conName locs tys argvals argtys) = do
  locVals <- mapM locationToValue locs
  untyped_argvals <- mapM eraseVal argvals
  return (UE.Constr conName locVals untyped_argvals)
-- eraseval (TE.Closure fvVals fvTys
eraseVal (TE.UnitM val) = do
  untyped_val <- eraseVal val
  return (UE.UnitM untyped_val)
eraseVal (TE.BindM bindingDecls expr) = do
  untyped_bindingDecls <- mapM eraseBindingDecl bindingDecls
  untyped_expr <- erase expr
  return (UE.BindM untyped_bindingDecls untyped_expr)
eraseVal (TE.Req fn ty arg) = do
  untyped_fn <- eraseVal fn
  untyped_arg <- eraseVal arg
  return (UE.Req untyped_fn untyped_arg)
eraseVal (TE.Call fn ty arg) = do
  untyped_fn <- eraseVal fn
  untyped_arg <- eraseVal arg
  return (UE.Call untyped_fn untyped_arg)
--
-- TODO:
-- 
--   (1) Current location
--   (2) Comparising of the current location with loc
--   (3) let bidnings for untyped_fn and untyped_arg for not duplicating them
-- 
-- eraseVal (TE.GenApp loc fn ty arg) = do
--   locVal <- locationToValue loc
--   untyped_fn <- eraseVal fn
--   untyped_arg <- eraseVal arg
--   return (UE.Case locVal
--           (mkAlternatives
--            (UE.App untyped_fn untyped_arg)
--            (UE.Req untyped_fn untyped_arg)
--            (UE.Call untyped_fn untyped_arg)))


-----------------------------------
-- Convrsion of locations to values
-----------------------------------
locationToValue :: Location -> IO UE.Value
locationToValue (Location s)
 | isClient (Location s) = return $ UE.mkConstForLocation s
 | isServer (Location s) = return $ UE.mkConstForLocation s
 | otherwise = error $ "locationToValue: not supported location: " ++ s
locationToValue (LocVar x) = return $ UE.Var x

