{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Erase where

import Location
import qualified CSExpr as TE -- (Typed) Target expressions
import qualified UntypedCSExpr as UE  -- Untyped target expressions

---------------------------------------------
-- Erase types and locations from expressions
---------------------------------------------
erase :: Location -> TE.Expr -> IO UE.Expr

erase currentLoc (TE.ValExpr v) = do
  uv <- eraseVal currentLoc v
  return (UE.ValExpr uv)

erase currentLoc (TE.Let bindingDecls expr) = do
  untyped_bindingDecls <- mapM (eraseBindingDecl currentLoc) bindingDecls
  untyped_expr <- erase currentLoc expr
  return (UE.Let untyped_bindingDecls untyped_expr)

erase currentLoc (TE.Case val ty alts) = do
  untyped_val <- eraseVal currentLoc val
  untyped_alts <- mapM (eraseAlt currentLoc) alts
  return (UE.Case untyped_val untyped_alts)

erase currentLoc (TE.App fn ty arg) = do
  untyped_fn <- eraseVal currentLoc fn
  untyped_arg <- eraseVal currentLoc arg
  return (UE.App untyped_fn untyped_arg)

erase currentLoc (TE.TypeApp fn ty argtys) = do
  untyped_fn <- eraseVal currentLoc fn
  return $ UE.ValExpr untyped_fn

erase currentLoc (TE.LocApp fn ty arglocs) = do
  untyped_fn <- eraseVal currentLoc fn
  return $ UE.ValExpr untyped_fn

erase currentLoc (TE.Prim primOp locs tys vals) = do
  locVals <- mapM locationToValue locs
  untyped_vals <- mapM (eraseVal currentLoc) vals
  return (UE.Prim primOp locVals untyped_vals)

--
eraseBindingDecl :: Location -> TE.BindingDecl -> IO UE.BindingDecl

eraseBindingDecl currentLoc (TE.Binding x ty expr) = do
  untyped_expr <- erase currentLoc expr
  return (UE.Binding x untyped_expr)

--
eraseAlt :: Location -> TE.Alternative -> IO UE.Alternative

eraseAlt currentLoc (TE.Alternative conname xs expr) = do
  untyped_expr <- erase currentLoc expr
  return (UE.Alternative conname xs untyped_expr)

eraseAlt currentLoc (TE.TupleAlternative xs expr) = do
  untyped_expr <- erase currentLoc expr
  return (UE.TupleAlternative xs untyped_expr)
  

----------------------------------------
-- Erase types and locations from values
----------------------------------------
eraseVal :: Location -> TE.Value -> IO UE.Value

eraseVal currentLoc (TE.Var x) = return (UE.Var x)

eraseVal currentLoc (TE.Lit lit) = return (UE.Lit lit)

eraseVal currentLoc (TE.Tuple vals) = do
  untyped_vals <- mapM (eraseVal currentLoc) vals
  return (UE.Tuple untyped_vals)
  
eraseVal currentLoc (TE.Constr conName locs tys argvals argtys) = do
  locVals <- mapM locationToValue locs
  untyped_argvals <- mapM (eraseVal currentLoc) argvals
  return (UE.Constr conName locVals untyped_argvals)
  
-- eraseval currentLoc (TE.Closure fvVals fvTys

eraseVal currentLoc (TE.UnitM val) = do
  untyped_val <- eraseVal currentLoc val
  return (UE.UnitM untyped_val)
  
eraseVal currentLoc (TE.BindM bindingDecls expr) = do
  untyped_bindingDecls <- mapM (eraseBindingDecl currentLoc) bindingDecls
  untyped_expr <- erase currentLoc expr
  return (UE.BindM untyped_bindingDecls untyped_expr)
  
eraseVal currentLoc (TE.Req fn ty arg) = do
  untyped_fn <- eraseVal currentLoc fn
  untyped_arg <- eraseVal currentLoc arg
  return (UE.Req untyped_fn untyped_arg)
  
eraseVal currentLoc (TE.Call fn ty arg) = do
  untyped_fn <- eraseVal currentLoc fn
  untyped_arg <- eraseVal currentLoc arg
  return (UE.Call untyped_fn untyped_arg)
  
--
-- TODO:
-- 
--   (1) Current location [DONE]
--   (2) Comparising of the current location with loc
--   (3) let bidnings for untyped_fn and untyped_arg for not duplicating them
-- 
eraseVal currentLoc (TE.GenApp loc fn ty arg)
   | currentLoc == loc = do    -- if statically equivalent
       untyped_fn <- eraseVal currentLoc fn
       untyped_arg <- eraseVal currentLoc arg
       return (UE.BindM [UE.Binding "ret" (UE.App untyped_fn untyped_arg)] (UE.ValExpr $ UE.Var "ret"))
       
   | otherwise = do            -- if need to examine the equivalence dynamically

       locVal <- locationToValue loc
       untyped_fn <- eraseVal currentLoc fn
       untyped_arg <- eraseVal currentLoc arg
       return (UE.BindM [UE.Binding "ret" (UE.App untyped_fn untyped_arg)] (UE.ValExpr $ UE.Var "ret"))
       
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

