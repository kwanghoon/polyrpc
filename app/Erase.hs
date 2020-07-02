{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Erase where

import Location
import qualified CSExpr as TE -- (Typed) Target expressions
import qualified UntypedCSExpr as UE  -- Untyped target expressions

eraseProgram funStore expr = do
  untyped_expr <- erase clientLoc expr
  let clientstore = _clientstore funStore
  let serverstore = _serverstore funStore
  
  return (untyped_funStore, untyped_expr)

-------------
-- Erase code
-------------
eraseFunStore loc (name, (codetype, code)) = do
  untyped_code <- eraseCode loc code
  return (name, code)
  
eraseCode loc (TE.Code freeLocs freeTyvars freeVars opencode) =
  untyped_opencode <- eraseOpencode loc opencode
  return (UE.Code freeLocs freeVars untyped_opencode)

eraseOpencode loc (TE.CodeAbs xTys expr) = do
  untyped_expr <- erase loc expr
  return (UE.CodeAbs [x | (x,_) <- xTys] untyped_expr)

-- eraseOpencode loc (TE.CodeTypeAbs tyvars expr) = do
--   untyped_expr <- erase loc expr
--   return ???

-- eraseOpencode loc (TE.CodeLocAbs lovars expr) = do
--   untyped_expr <- erase loc expr
--   return ???

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

erase currentLoc (TE.LocApp fn ty arglocs) = do  -- Important!
  let locVals = map UE.locRep arglocs
  untyped_fn <- eraseVal currentLoc fn
  return $ foldl (\l r -> UE.Let [UE.Binding "$arg" l] (UE.App (UE.Var "$arg") r)) (UE.ValExpr untyped_fn) locVals

erase currentLoc (TE.Prim primOp locs tys vals) = do
  let locVals = map UE.locRep locs
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
  let locVals = map UE.locRep locs
  untyped_argvals <- mapM (eraseVal currentLoc) argvals
  return (UE.Constr conName locVals untyped_argvals)
  
eraseVal currentLoc (TE.Closure fvVals fvTys (TE.CodeName name locs tys) recChumNames) = do
  let locVals = map UE.locRep locs
  untyped_fvVals <- mapM (eraseVal currentLoc) fvVals
  return (UE.Closure untyped_fvVals (UE.CodeName name locVals) recChumNames)

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
  
eraseVal currentLoc (TE.GenApp loc fn ty arg)
   | currentLoc == loc = do    -- if statically equivalent
       untyped_fn <- eraseVal currentLoc fn
       untyped_arg <- eraseVal currentLoc arg
       return (UE.BindM [UE.Binding "$result" (UE.App untyped_fn untyped_arg)] (UE.ValExpr $ UE.Var "$result"))
       
   | otherwise = do            -- if need to examine the equivalence dynamically
       let currentLocVal = UE.locRep currentLoc
       let locVal = UE.locRep loc
       untyped_fn <- eraseVal currentLoc fn
       untyped_arg <- eraseVal currentLoc arg
       
       return $ UE.BindM [UE.Binding "$result"
         (UE.ifThenElse
            (UE.equalLoc currentLoc currentLocVal locVal)
            (UE.App untyped_fn untyped_arg)
            (UE.ifThenElse
               (UE.equalLoc currentLoc locVal (UE.locRep serverLoc))
               (UE.ValExpr (UE.Req untyped_fn untyped_arg))
               (UE.ValExpr (UE.Call untyped_fn untyped_arg))))] (UE.ValExpr (UE.Var "$result"))
