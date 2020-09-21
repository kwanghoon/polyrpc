module Simpl (simpl) where

import Location
import Prim
import Literal
import CSType
import CSExpr

import Control.Monad
import Data.HashMap.Strict as H
import Data.List as L
import Data.Maybe as M

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

addVar :: String -> UseInfo -> UseInfo
addVar x useInfo =
  useInfo { varUseInfo = H.insert x 0 (varUseInfo useInfo) }

addVars :: [String] -> UseInfo -> UseInfo
addVars xs useInfo =
  foldl (\useInfo x -> addVar x useInfo) useInfo xs

rmVar :: String -> UseInfo -> UseInfo
rmVar x useInfo =
  useInfo { varUseInfo = H.delete x (varUseInfo useInfo) }

rmVars :: [String] -> UseInfo -> UseInfo
rmVars xs useInfo =
  foldl (\useInfo x -> rmVar x useInfo) useInfo xs
  
incVar :: String -> UseInfo -> UseInfo
incVar x useInfo =
  case H.lookup x (varUseInfo useInfo) of
    Nothing    -> addVar x useInfo
    Just count ->
      let varUseInfo' = H.insert x (count+1) (varUseInfo useInfo) in
        useInfo { varUseInfo = varUseInfo' }

save :: UseInfo -> [String] -> [(String, Int)]
save useInfo xs =
  [ (x, M.fromJust z) | x <- xs, let z = H.lookup x hashmap, M.isJust z ]
  where
    hashmap = varUseInfo useInfo

restore :: [(String, Int)] -> UseInfo -> UseInfo
restore xUseList useInfo =
  useInfo { varUseInfo = foldl fXUseList hashmap xUseList }
  where
    hashmap = varUseInfo useInfo

    fXUseList hashmap (x,count) = H.insert x count hashmap


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
      foldl (\hash x -> H.insert x 0 hash) empty
       ([ codeName | (codeName, _) <- _clientstore funStore ] ++
        [ codeName | (codeName, _) <- _serverstore funStore ])
  , varUseInfo = empty }

--
doExpr :: Monad m => UseInfo -> Expr -> m (UseInfo, Expr)
doExpr useInfo (ValExpr v) = do
  (useInfo', v') <- doValue useInfo v
  return (useInfo', ValExpr v')
  
doExpr useInfo (Let bindDecls expr) = do
  let savedInfo = save useInfo xs

  let useInfo0 = addVars xs useInfo
  (useInfo1, bindDecls1) <- foldM fBindDecl (useInfo0, []) bindDecls
  (useInfo2, expr1) <- doExpr useInfo1 expr
  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  let useInfo3 = rmVars xs useInfo2
  
  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, Let bindDecls1 expr1)
  
  where
    fBindDecl (useInfo, bindDecls) (Binding x ty bexpr) = do
      (useInfo', bexpr') <- doExpr useInfo bexpr
      return (useInfo', bindDecls ++ [Binding x ty bexpr'])

    xs = L.map (\(Binding x ty expr) -> x) bindDecls

doExpr useInfo (Case v ty alts) = do
  (useInfo1, v1) <- doValue useInfo v
  (useInfo2, alts1) <- foldM fAlt (useInfo1, []) alts
  return (useInfo2, Case v1 ty alts1)

  where
    fAlt (useInfo, alts) (Alternative cname xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = addVars xs useInfo
      (useInfo1, expr1) <- doExpr useInfo0 expr
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [Alternative cname xs expr1])
      
    fAlt (useInfo, alts) (TupleAlternative xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = addVars xs useInfo
      (useInfo1, expr1) <- doExpr useInfo0 expr
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [TupleAlternative xs expr])

doExpr useInfo (App v ty arg) = do
  (useInfo1, v1) <- doValue useInfo v
  (useInfo2, arg1) <- doValue useInfo1 arg
  return (useInfo2, App v1 ty arg1)
  
doExpr useInfo (TypeApp v ty tys) = do
  (useInfo1, v1) <- doValue useInfo v
  return (useInfo1, TypeApp v1 ty tys)
  
doExpr useInfo (LocApp v ty locs) = do
  (useInfo1, v1) <- doValue useInfo v
  return (useInfo1, LocApp v1 ty locs)
  
doExpr useInfo (Prim op locs tys vs) = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) vs
  return (useInfo1, Prim op locs tys vs1)

  where
    fVs (useInfo, vs) v = do
      (useInfo', v') <- doValue useInfo v
      return (useInfo', vs ++ [v'])

--
doValue :: Monad m => UseInfo -> Value -> m (UseInfo, Value)
doValue useInfo (Var x) =
  return (incVar x useInfo, Var x)
  
doValue useInfo (Lit x) =
  return (useInfo, Lit x)
  
doValue useInfo (Tuple vs) = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) vs
  return (useInfo1, Tuple vs1)
  
  where
    fVs (useInfo, vs) v = do
      (useInfo', v') <- doValue useInfo v
      return (useInfo', vs ++ [v'])
      
doValue useInfo (Constr cname locs tys vs tys') = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) vs
  return (useInfo1, Constr cname locs tys vs1 tys')
  
  where
    fVs (useInfo, vs) v = do
      (useInfo', v') <- doValue useInfo v
      return (useInfo', vs ++ [v'])
      
doValue useInfo (Closure vs tys cname optrecs) = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) vs
  return (useInfo1, Closure vs1 tys cname optrecs)
  
  where
    fVs (useInfo, vs) v = do
      (useInfo', v') <- doValue useInfo v
      return (useInfo', vs ++ [v'])
      
doValue useInfo (UnitM v) = do
  (useInfo1, v1) <- doValue useInfo v
  return (useInfo1, UnitM v1)
  
doValue useInfo (BindM bindDecls expr) = do
  let savedInfo = save useInfo xs

  let useInfo0 = addVars xs useInfo
  (useInfo1, bindDecls1) <- foldM fBindDecl (useInfo0, []) bindDecls
  (useInfo2, expr1) <- doExpr useInfo1 expr
  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  let useInfo3 = rmVars xs useInfo2

  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, BindM bindDecls1 expr1)

  where
    fBindDecl (useInfo, bindDecls) (Binding x ty bexpr) = do
      (useInfo', bexpr') <- doExpr useInfo bexpr
      return (useInfo', bindDecls ++ [Binding x ty bexpr'])

    xs = L.map (\(Binding x ty expr) -> x) bindDecls      
  
doValue useInfo (Req v ty arg) = do
  (useInfo1, v1) <- doValue useInfo v
  (useInfo2, arg1) <- doValue useInfo1 arg
  return (useInfo2, Req v1 ty arg1)
  
doValue useInfo (Call v ty arg) = do
  (useInfo1, v1) <- doValue useInfo v
  (useInfo2, arg1) <- doValue useInfo1 arg
  return (useInfo2, Call v1 ty arg1)
  
doValue useInfo (GenApp loc v ty arg) = do
  (useInfo1, v1) <- doValue useInfo v
  (useInfo2, arg1) <- doValue useInfo1 arg
  return (useInfo2, GenApp loc v1 ty arg1)

--
doFunStore :: Monad m => UseInfo -> FunctionStore -> m FunctionStore
doFunStore useInfo funStore =
  -- 1. do Use Analysis
  -- 2. Delete unused codes
  return funStore

