module Simpl (simpl) where

import Location
import Prim
import Literal
import CSType
import CSExpr

import Data.HashMap.Strict

---------------------------------------------------------------------------
-- Simplification:
--
--   (1) simplify bound unit values
--      : BindM [ Binding x ty (ValExpr (UnitM v)) ] expr  ===>  expr [v/x]
--   (2) delete unused bound variables and function names
---------------------------------------------------------------------------

--
data UseInfo =
  UseInfo { cNameUseInfo :: HashMap String Int
          , varUseInfo   :: HashMap String Int }

initUseInfo = UseInfo { cNameUseInfo = empty, varUseInfo = empty }

---------------------
-- Simplify CS programs
---------------------

simpl :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr
                     -> m (GlobalTypeInfo, FunctionStore, Expr)
simpl gti funStore mainexpr = do
  let initUseInfo = initUseInfoFrom funStore
  (useInfo, mainexpr') <-doExpr initUseInfo mainexpr
  funStore' <- doFunStore useInfo funStore
  return (gti, funStore', mainexpr')

initUseInfoFrom :: FunctionStore -> UseInfo
initUseInfoFrom funStore = UseInfo
  { cNameUseInfo =
      foldl (\hash x -> insert x 0 hash) empty
       ([ codeName | (codeName, _) <- _clientstore funStore ] ++
        [ codeName | (codeName, _) <- _serverstore funStore ])
  , varUseInfo = empty }

--
doExpr :: Monad m => UseInfo -> Expr -> m (UseInfo, Expr)
doExpr useInfo (ValExpr v) = do
  (useInfo', v') <- doValue useInfo v
  return (useInfo', ValExpr v')
doExpr useInfo (Let bindDecls expr) =
  return (useInfo, Let bindDecls expr)
doExpr useInfo (App v ty arg) =
  return (useInfo, App v ty arg)
doExpr useInfo (TypeApp v ty tys) =
  return (useInfo, TypeApp v ty tys)
doExpr useInfo (LocApp v ty locs) =
  return (useInfo, LocApp v ty locs)
doExpr useInfo (Prim op locs tys vs) =
  return (useInfo, Prim op locs tys vs)

--
doValue :: Monad m => UseInfo -> Value -> m (UseInfo, Value)
doValue useInfo (Var x) =
  return (useInfo, Var x)
doValue useInfo (Lit x) =
  return (useInfo, Lit x)
doValue useInfo (Tuple vs) =
  return (useInfo, Tuple vs)
doValue useInfo (Constr cname locs tys vs tys') =
  return (useInfo, Constr cname locs tys vs tys')
doValue useInfo (Closure vs tys cname optrecs) =
  return (useInfo, Closure vs tys cname optrecs)
doValue useInfo (UnitM v) =
  return (useInfo, UnitM v)
doValue useInfo (BindM bindDecls expr) =
  return (useInfo, BindM bindDecls expr)
doValue useInfo (Req v ty arg) =
  return (useInfo, Req v ty arg)
doValue useInfo (Call v ty arg) =
  return (useInfo, Call v ty arg)
doValue useInfo (GenApp loc v ty arg) =
  return (useInfo, GenApp loc v ty arg)

--
doFunStore :: Monad m => UseInfo -> FunctionStore -> m FunctionStore
doFunStore useInfo funStore =
  -- 1. do Use Analysis
  -- 2. Delete unused codes
  return funStore

