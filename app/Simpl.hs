module Simpl (simpl) where

import Location
import Prim
import Literal
import CSType
import CSExpr
import CSSubst

import Control.Monad
import Data.HashMap.Strict as H
import Data.List as L
import Data.Maybe as M

import Debug.Trace

---------------------------------------------------------------------------
-- Simplification:
--
--   (1) simplify bound unit values
--      : BindM [ Binding False x ty (ValExpr (UnitM v)) ] expr  ===>  expr [v/x]
--   (2) delete unused bound variables and function names
---------------------------------------------------------------------------

--
data UseInfo =
  UseInfo { cNameUseInfo :: HashMap String Int
          , varUseInfo   :: HashMap String Int }

initUseInfo = UseInfo { cNameUseInfo = empty, varUseInfo = empty }

addVar :: String -> UseInfo -> UseInfo
addVar x useInfo =
  useInfo { varUseInfo = H.insert x 1 (varUseInfo useInfo) }

initVars :: [(String, Bool)] -> UseInfo -> UseInfo
initVars xIsTops useInfo =
  foldl (\useInfo (x,istop) ->
    let initCount = if istop then 2 else 0
        _varUseInfo = H.insert x initCount (varUseInfo useInfo)
    in  useInfo { varUseInfo = _varUseInfo }) useInfo xIsTops

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


incCodeName :: String -> UseInfo -> UseInfo
incCodeName x useInfo =
  case H.lookup x (cNameUseInfo useInfo) of
    Nothing ->
      let cNameUseInfo' = H.insert x 1 (cNameUseInfo useInfo) in
        useInfo { cNameUseInfo = cNameUseInfo' }
    Just count ->
      let cNameUseInfo' = H.insert x (count+1) (cNameUseInfo useInfo) in
        useInfo { cNameUseInfo = cNameUseInfo' }

---------------------
-- Simplify CS programs
---------------------

simpl :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr
                     -> m (GlobalTypeInfo, FunctionStore, Expr)
simpl gti funStore mainexpr =
  -- return (gti, funStore, mainexpr)
  -- trace (show mainexpr ++ "\n")
  _simpl gti funStore mainexpr 1000  -- To prevent the infinite loop!

_simpl gti funStore mainexpr 0 = do
  return (gti, funStore, mainexpr)

_simpl gti funStore mainexpr n = do
  let initUseInfo = initUseInfoFrom funStore
  (useInfo, mainexpr', changed1) <- doExpr initUseInfo mainexpr (MonType unit_type)
  (useInfo1, funStore', changed2) <- doFunStore useInfo funStore

  -- trace (show (cNameUseInfo useInfo1) ++ "\n")
  --  (trace (show changed1 ++ " " ++ show changed2 ++ "\n" ++ show mainexpr' ++ "\n")
  --   (trace (show funStore' ++ "\n"))
  (if changed1 || changed2
      then _simpl gti funStore' mainexpr' (n-1)
      else return (gti, funStore', mainexpr'))

initUseInfoFrom :: FunctionStore -> UseInfo
initUseInfoFrom funStore = UseInfo
     { cNameUseInfo = empty, varUseInfo = empty }

-- initUseInfoFrom funStore = UseInfo
--   { cNameUseInfo =
--       foldl (\hash x -> H.insert x 0 hash) empty
--        ([ codeName | (codeName, _) <- _clientstore funStore ] ++
--         [ codeName | (codeName, _) <- _serverstore funStore ])
--   , varUseInfo = empty }

--
doExpr :: Monad m => UseInfo -> Expr -> Type -> m (UseInfo, Expr, Bool)
doExpr useInfo (ValExpr v) exprty = do
  (useInfo', v', changed) <- doValue useInfo v exprty
  return (useInfo', ValExpr v', changed)

doExpr useInfo (Let bindDecls expr) exprty = do
  let savedInfo = save useInfo xs

  let useInfo0 = initVars xIsTops useInfo
  (useInfo1, bindDecls1, changed1) <- foldM fBindDecl (useInfo0, [], False) bindDecls
  (useInfo2, expr1, changed2) <- doExpr useInfo1 expr exprty

  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  (expr2, changed3) <- doSubstLet useInfo2 bindDecls1 expr1 exprty
  -------------------------------------

  let useInfo3 = rmVars xs useInfo2

  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, expr2, changed1 || changed2 || changed3)

  where
    fBindDecl (useInfo, bindDecls, changed) (Binding istop x ty bexpr) = do
      (useInfo', bexpr', changed') <- doExpr useInfo bexpr ty
      return (useInfo', bindDecls ++ [Binding istop x ty bexpr'], changed || changed')

    xIsTops = L.map (\(Binding istop x ty expr) -> (x,istop)) bindDecls
    xs = L.map fst xIsTops

doExpr useInfo (Case v ty alts) exprty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  (useInfo2, alts1, changed2) <- foldM fAlt (useInfo1, [], False) alts
  return (useInfo2, Case v1 ty alts1, changed1 || changed2)

  where
    fAlt (useInfo, alts, changed) (Alternative c xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = initVars (zip xs (repeat False)) useInfo
      (useInfo1, expr1, changed1) <- doExpr useInfo0 expr exprty
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [Alternative c xs expr1], changed || changed1)

    fAlt (useInfo, alts, changed) (TupleAlternative xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = initVars (zip xs (repeat False)) useInfo
      (useInfo1, expr1, changed1) <- doExpr useInfo0 expr exprty
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [TupleAlternative xs expr], changed || changed1)

doExpr useInfo (App v ty@(CloType (FunType argty _ _)) arg) exprty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  (useInfo2, arg1, changed2) <- doValue useInfo1 arg argty
  return (useInfo2, App v1 ty arg1, changed1 || changed2)

doExpr useInfo (TypeApp v ty tys) exprty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  return (useInfo1, TypeApp v1 ty tys, changed1)

doExpr useInfo (LocApp v ty locs) exprty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  return (useInfo1, LocApp v1 ty locs, changed1)

doExpr useInfo (Prim MkRecOp locs tys vs@[Var recvar, _]) exprty = do
  let useInfo1 = incVar recvar (incVar recvar useInfo) -- #(recvr)=2
  return (useInfo1, Prim MkRecOp locs tys vs, False)

doExpr useInfo (Prim prim op_locs op_tys vs) exprty =
  case lookupPrimOpType prim of
    [] -> error $ "[Simpl:doExpr] Not found prim: " ++ show prim
    ((locvars, tyvars, argtys, _):_) -> do
      let substTy = zip tyvars op_tys
      let substLoc = zip locvars op_locs
      let substed_argtys = L.map (doSubstLoc substLoc . doSubst substTy) argtys

      (useInfo1, vs1, changed1) <- foldM fVs (useInfo, [], False) (zip vs argtys)
      return (useInfo1, Prim prim op_locs op_tys vs1, changed1)

  where
    fVs (useInfo, vs, changed) (v, vty) = do
      (useInfo', v', changed') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'], changed || changed')

--
doValue :: Monad m => UseInfo -> Value -> Type -> m (UseInfo, Value, Bool)
doValue useInfo (Var x) valty =
  return (incVar x useInfo, Var x, False)

doValue useInfo (Lit x) valty =
  return (useInfo, Lit x, False)

doValue useInfo (Tuple vs) (TupleType tys) = do
  (useInfo1, vs1, changed1) <- foldM fVs (useInfo, [], False) (zip vs tys)
  return (useInfo1, Tuple vs1, changed1)

  where
    fVs (useInfo, vs, changed) (v, vty) = do
      (useInfo', v', changed') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'], changed || changed')

doValue useInfo (Constr cname locs tys vs vstys) valty = do
  (useInfo1, vs1, changed1) <- foldM fVs (useInfo, [], False) (zip vs vstys)
  return (useInfo1, Constr cname locs tys vs1 vstys, changed1)

  where
    fVs (useInfo, vs, changed) (v, vty) = do
      (useInfo', v', changed') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'], changed || changed')

doValue useInfo (Closure vs vstys cname optrecs) vty = do
  let useInfo0 = incCodeName (getCodeName cname) useInfo
  (useInfo1, vs1, changed1) <- foldM fVs (useInfo0, [], False) (zip vs vstys)
  return (useInfo1, Closure vs1 vstys cname optrecs, changed1)

  where
    fVs (useInfo, vs, changed) (v, vty) = do
      (useInfo', v', changed') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'], changed || changed')

doValue useInfo (UnitM v) (MonType vty) = do
  (useInfo1, v1, changed1) <- doValue useInfo v vty
  return (useInfo1, UnitM v1, changed1)

doValue useInfo (BindM bindDecls expr) (MonType exprty) = do
  let savedInfo = save useInfo xs

  let useInfo0 = initVars xIsTops useInfo
  (useInfo1, bindDecls1, changed1) <- foldM fBindDecl (useInfo0, [], False) bindDecls
  (useInfo2, expr1, changed2) <- doExpr useInfo1 expr (MonType exprty)
  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  (value2, changed3) <- doSubstBindM useInfo2 bindDecls1 expr1 (MonType exprty)
  -------------------------------------
  let useInfo3 = rmVars xs useInfo2

  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, value2, changed1 || changed2 || changed3)

  where
    fBindDecl (useInfo, bindDecls, changed) (Binding istop x ty bexpr) = do
      (useInfo', bexpr', changed') <- doExpr useInfo bexpr (MonType ty)
      return (useInfo', bindDecls ++ [Binding istop x ty bexpr'], changed || changed')

    xIsTops = L.map (\(Binding istop x ty expr) -> (x,istop)) bindDecls
    xs = L.map fst xIsTops

doValue useInfo (Req v ty@(CloType (FunType argty _ _)) arg) valty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  (useInfo2, arg1, changed2) <- doValue useInfo1 arg argty
  return (useInfo2, Req v1 ty arg1, changed1 || changed2)

doValue useInfo (Call v ty@(CloType (FunType argty _ _)) arg) valty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  (useInfo2, arg1, changed2) <- doValue useInfo1 arg argty
  return (useInfo2, Call v1 ty arg1, changed1 || changed2)

doValue useInfo (GenApp loc v ty@(CloType (FunType argty _ _))  arg) valty = do
  (useInfo1, v1, changed1) <- doValue useInfo v ty
  (useInfo2, arg1, changed2) <- doValue useInfo1 arg argty
  return (useInfo2, GenApp loc v1 ty arg1, changed1 || changed2)

doValue useInfo val valty =
  error $ "[Simpl] doValue " ++ show val ++ " : " ++ show valty

--
doSubstLet :: Monad m => UseInfo -> [BindingDecl] -> Expr -> Type -> m (Expr, Bool)
doSubstLet useInfo bindDecls expr exprty = do
  (bindDecls1, expr1, changed1) <- doSubstBindDecls useInfo bindDecls expr exprty
  case bindDecls1 of
    [] -> return (expr1, changed1) -- not L.null bindDecls ??
    _  -> return (Let bindDecls1 expr1, changed1)

doSubstBindM :: Monad m => UseInfo -> [BindingDecl] -> Expr -> Type -> m (Value, Bool)
doSubstBindM useInfo bindDecls expr exprty@(MonType valty) = do
  (bindDecls1, expr1, changed1) <- doSubstBindDecls useInfo bindDecls expr exprty
  case (bindDecls1, expr1) of
    ([], ValExpr val) -> return (val, changed1)
    ([], _) -> return (BindM [Binding False "$x" valty expr1]  --Todo: infinite loop!!
                      (ValExpr (UnitM (Var "$x")))
                      , changed1)
    (_ , _) -> return (BindM bindDecls1 expr1, changed1)

--
doSubstBindDecls :: Monad m => UseInfo -> [BindingDecl]
                     -> Expr -> Type -> m ([BindingDecl], Expr, Bool)
doSubstBindDecls useInfo bindDecls expr exprty = do
  (bindDecls1, expr1, changed1) <- foldM fBindDecl ([], expr, False) bindDecls
  return (bindDecls1, expr1, changed1)

  where
    fBindDecl (bindDecls, expr, changed) binding@(Binding istop x ty (ValExpr (UnitM v))) =
      -- trace (let z = (fromJust (H.lookup x (varUseInfo useInfo)))
      --        in  if z <= 1
      --            then ("[1st] " ++ show z ++ " : " ++ x ++ " = " ++ show binding ++ "\n\t" ++ show (doSubstExpr [(x,v)] expr))
      --            else "")
      (case H.lookup x (varUseInfo useInfo) of
        Nothing  -> error "What?" -- return (bindDecls, expr)  -- dead code elimination
        Just 0   -> return (bindDecls, expr, True)  -- dead code elimination
        Just 1   -> return (bindDecls, doSubstExpr [(x,v)] expr, True)  -- inlining
        Just cnt -> return (bindDecls++[binding], expr, changed))  -- do nothing

    fBindDecl (bindDecls, expr, changed) binding@(Binding istop x ty _) =
      -- trace (if (fromJust (H.lookup x (varUseInfo useInfo)) <= 1) then ("[2nd]" ++ x ++ " = " ++ show binding) else "")
      return (bindDecls++[binding], expr, changed)

--
doFunStore :: Monad m => UseInfo -> FunctionStore -> m (UseInfo, FunctionStore, Bool)
doFunStore useInfo funStore = do
  -- 1. do Use analysis
  (useInfo1, clientstore1, changed1)
     <- foldM fStore (useInfo, [], False) (_clientstore funStore)
  (useInfo2, serverstore1, changed2)
     <- foldM fStore (useInfo1, [], False) (_serverstore funStore)

  -- 2. Do deadcode elimination
  let elim = fElim useInfo2

  (clientstore2, changed3) <- foldM elim ([], False) clientstore1
  (serverstore2, changed4) <- foldM elim ([], False) serverstore1

  -- error $ "Deadcode elimination: " ++ show (cNameUseInfo useInfo2)
  return (useInfo2
         , funStore {_clientstore=clientstore2} {_serverstore=serverstore2}
         , changed1 || changed2 || changed3 || changed4)

  where
    fStore (useInfo, store, changed) (name, codeTypeCode) = do
      (useInfo1, codeTypeCode1, changed1) <- doCode useInfo codeTypeCode
      return (useInfo1, store++[(name, codeTypeCode1)], changed || changed1)

    fElim useInfo (store, changed) namedCode@(name, _) =
      case H.lookup name (cNameUseInfo useInfo) of
        Nothing -> return (store, True) -- dead code elimination
        Just 0  -> return (store, True) -- dead code elimination
        Just _  -> return $ (store ++ [namedCode], changed) -- do nothing

doCode :: Monad m => UseInfo -> (CodeType, Code) -> m (UseInfo, (CodeType, Code), Bool)
doCode useInfo (CodeType as1 ls1 tys ty, Code ls2 as2 vs opencode) = do
  (useInfo1, opencode1, changed) <- doOpenCode useInfo opencode ty
  return (useInfo1, (CodeType as1 ls1 tys ty, Code ls2 as2 vs opencode1), changed)

doOpenCode :: Monad m => UseInfo -> OpenCode -> Type -> m (UseInfo, OpenCode, Bool)
doOpenCode useInfo (CodeAbs xTys expr) (FunType _ _ resty) = do
  (useInfo1, expr1, changed1) <- doExpr useInfo expr resty
  return (useInfo1, CodeAbs xTys expr1, changed1)
doOpenCode useInfo (CodeTypeAbs tyvars expr) (TypeAbsType _ bodyty) = do
  (useInfo1, expr1, changed1) <- doExpr useInfo expr bodyty
  return (useInfo1, CodeTypeAbs tyvars expr1, changed1)
doOpenCode useInfo (CodeLocAbs locvars expr) (LocAbsType _ bodyty) = do
  (useInfo1, expr1, changed1) <- doExpr useInfo expr bodyty
  return (useInfo1, CodeLocAbs locvars expr1, changed1)
