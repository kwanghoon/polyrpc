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


addCodeName :: String -> UseInfo -> UseInfo
addCodeName x useInfo =
  useInfo { cNameUseInfo = H.insert x 0 (cNameUseInfo useInfo) }

incCodeName :: String -> UseInfo -> UseInfo
incCodeName x useInfo =
  case H.lookup x (cNameUseInfo useInfo) of
    Nothing -> addCodeName x useInfo
    Just count ->
      let cNameUseInfo' = H.insert x (count+1) (cNameUseInfo useInfo) in
        useInfo { cNameUseInfo = cNameUseInfo' }

---------------------
-- Simplify CS programs
---------------------

simpl :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr
                     -> m (GlobalTypeInfo, FunctionStore, Expr)
simpl gti funStore mainexpr = do
  let initUseInfo = initUseInfoFrom funStore
  (useInfo, mainexpr') <-doExpr initUseInfo mainexpr (MonType unit_type)
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
doExpr :: Monad m => UseInfo -> Expr -> Type -> m (UseInfo, Expr)
doExpr useInfo (ValExpr v) exprty = do
  (useInfo', v') <- doValue useInfo v exprty
  return (useInfo', ValExpr v')

doExpr useInfo (Let bindDecls expr) exprty = do
  let savedInfo = save useInfo xs

  let useInfo0 = addVars xs useInfo
  (useInfo1, bindDecls1) <- foldM fBindDecl (useInfo0, []) bindDecls
  (useInfo2, expr1) <- doExpr useInfo1 expr exprty

  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  expr2 <- doSubstLet useInfo2 bindDecls1 expr1 exprty
  -------------------------------------

  let useInfo3 = rmVars xs useInfo2

  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, expr2)

  where
    fBindDecl (useInfo, bindDecls) (Binding x ty bexpr) = do
      (useInfo', bexpr') <- doExpr useInfo bexpr ty
      return (useInfo', bindDecls ++ [Binding x ty bexpr'])

    xs = L.map (\(Binding x ty expr) -> x) bindDecls

doExpr useInfo (Case v ty alts) exprty = do
  (useInfo1, v1) <- doValue useInfo v ty
  (useInfo2, alts1) <- foldM fAlt (useInfo1, []) alts
  return (useInfo2, Case v1 ty alts1)

  where
    fAlt (useInfo, alts) (Alternative cname xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = addVars xs useInfo
      (useInfo1, expr1) <- doExpr useInfo0 expr exprty
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [Alternative cname xs expr1])

    fAlt (useInfo, alts) (TupleAlternative xs expr) = do
      let savedInfo = save useInfo xs

      let useInfo0 = addVars xs useInfo
      (useInfo1, expr1) <- doExpr useInfo0 expr exprty
      let useInfo2 = rmVars xs useInfo1

      let useInfo3 = restore savedInfo useInfo2
      return (useInfo3, alts ++ [TupleAlternative xs expr])

doExpr useInfo (App v ty@(CloType (FunType argty _ _)) arg) exprty = do
  (useInfo1, v1) <- doValue useInfo v ty
  (useInfo2, arg1) <- doValue useInfo1 arg argty
  return (useInfo2, App v1 ty arg1)

doExpr useInfo (TypeApp v ty tys) exprty = do
  (useInfo1, v1) <- doValue useInfo v ty
  return (useInfo1, TypeApp v1 ty tys)

doExpr useInfo (LocApp v ty locs) exprty = do
  (useInfo1, v1) <- doValue useInfo v ty
  return (useInfo1, LocApp v1 ty locs)

doExpr useInfo (Prim MkRecOp locs tys vs@[Var recvar, _]) exprty = do
  let useInfo1 = incVar recvar (incVar recvar useInfo) -- #(recvr)=2
  return (useInfo1, Prim MkRecOp locs tys vs)

doExpr useInfo (Prim prim op_locs op_tys vs) exprty =
  case lookupPrimOpType prim of
    [] -> error $ "[Simpl:doExpr] Not found prim: " ++ show prim
    ((locvars, tyvars, argtys, _):_) -> do
      let substTy = zip tyvars op_tys
      let substLoc = zip locvars op_locs
      let substed_argtys = L.map (doSubstLoc substLoc . doSubst substTy) argtys

      (useInfo1, vs1) <- foldM fVs (useInfo, []) (zip vs argtys) -- vs. argtys
      return (useInfo1, Prim prim op_locs op_tys vs1)

  where
    fVs (useInfo, vs) (v, vty) = do
      (useInfo', v') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'])

--
doValue :: Monad m => UseInfo -> Value -> Type -> m (UseInfo, Value)
doValue useInfo (Var x) valty =
  return (incVar x useInfo, Var x)

doValue useInfo (Lit x) valty =
  return (useInfo, Lit x)

doValue useInfo (Tuple vs) (TupleType tys) = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) (zip vs tys)
  return (useInfo1, Tuple vs1)

  where
    fVs (useInfo, vs) (v, vty) = do
      (useInfo', v') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'])

doValue useInfo (Constr cname locs tys vs vstys) valty = do
  (useInfo1, vs1) <- foldM fVs (useInfo, []) (zip vs vstys)
  return (useInfo1, Constr cname locs tys vs1 vstys)

  where
    fVs (useInfo, vs) (v, vty) = do
      (useInfo', v') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'])

doValue useInfo (Closure vs vstys cname optrecs) vty = do
  let useInfo1 = incCodeName (getCodeName cname) useInfo
  (useInfo2, vs1) <- foldM fVs (useInfo1, []) (zip vs vstys)
  return (useInfo2, Closure vs1 vstys cname optrecs)

  where
    fVs (useInfo, vs) (v, vty) = do
      (useInfo', v') <- doValue useInfo v vty
      return (useInfo', vs ++ [v'])

doValue useInfo (UnitM v) (MonType vty) = do
  (useInfo1, v1) <- doValue useInfo v vty
  return (useInfo1, UnitM v1)

doValue useInfo (BindM bindDecls expr) (MonType exprty) = do
  let savedInfo = save useInfo xs

  let useInfo0 = addVars xs useInfo
  (useInfo1, bindDecls1) <- foldM fBindDecl (useInfo0, []) bindDecls
  (useInfo2, expr1) <- doExpr useInfo1 expr (MonType exprty)
  -------------------------------------
  -- This is where inlining is applied.
  -------------------------------------
  value2 <- doSubstBindM useInfo2 bindDecls1 expr1 (MonType exprty)
  -------------------------------------
  let useInfo3 = rmVars xs useInfo2

  let useInfo4 = restore savedInfo useInfo3
  return (useInfo4, value2)

  where
    fBindDecl (useInfo, bindDecls) (Binding x ty bexpr) = do
      (useInfo', bexpr') <- doExpr useInfo bexpr (MonType ty)
      return (useInfo', bindDecls ++ [Binding x ty bexpr'])

    xs = L.map (\(Binding x ty expr) -> x) bindDecls

doValue useInfo (Req v ty@(CloType (FunType argty _ _)) arg) valty = do
  (useInfo1, v1) <- doValue useInfo v ty
  (useInfo2, arg1) <- doValue useInfo1 arg argty
  return (useInfo2, Req v1 ty arg1)

doValue useInfo (Call v ty@(CloType (FunType argty _ _)) arg) valty = do
  (useInfo1, v1) <- doValue useInfo v ty
  (useInfo2, arg1) <- doValue useInfo1 arg argty
  return (useInfo2, Call v1 ty arg1)

doValue useInfo (GenApp loc v ty@(CloType (FunType argty _ _))  arg) valty = do
  (useInfo1, v1) <- doValue useInfo v ty
  (useInfo2, arg1) <- doValue useInfo1 arg argty
  return (useInfo2, GenApp loc v1 ty arg1)

doValue useInfo val valty =
  error $ "[Simpl] doValue " ++ show val ++ " : " ++ show valty

--
doSubstLet :: Monad m => UseInfo -> [BindingDecl] -> Expr -> Type -> m Expr
doSubstLet useInfo bindDecls expr exprty = do
  (bindDecls1, expr1) <- doSubstBindDecls useInfo bindDecls expr exprty
  case bindDecls1 of
    [] -> return expr1
    _  -> return (Let bindDecls1 expr1)

doSubstBindM :: Monad m => UseInfo -> [BindingDecl] -> Expr -> Type -> m Value
doSubstBindM useInfo bindDecls expr exprty@(MonType valty) = do
  (bindDecls1, expr1) <- doSubstBindDecls useInfo bindDecls expr exprty
  case bindDecls1 of
    [] -> return (BindM [Binding "$x" valty expr1] (ValExpr (UnitM (Var "$x"))))
    _  -> return (BindM bindDecls1 expr1)

--
doSubstBindDecls :: Monad m => UseInfo -> [BindingDecl]
                     -> Expr -> Type -> m ([BindingDecl], Expr)
doSubstBindDecls useInfo bindDecls expr exprty = do
  (bindDecls1, expr1) <- foldM fBindDecl ([], expr) bindDecls
  return (bindDecls1, expr1)

  where
    fBindDecl (bindDecls, expr) binding@(Binding x ty (ValExpr (UnitM v))) =
      case H.lookup x (varUseInfo useInfo) of
        Nothing  -> error "What?" -- return (bindDecls, expr)  -- dead code elimination
        Just 0   -> return (bindDecls, expr)  -- dead code elimination
        Just 1   -> return (bindDecls, doSubstExpr [(x,v)] expr)  -- inlining
        Just cnt -> return (bindDecls++[binding], expr)  -- do nothing

    fBindDecl (bindDecls, expr) binding =
      return (bindDecls++[binding], expr)

--
doFunStore :: Monad m => UseInfo -> FunctionStore -> m FunctionStore
doFunStore useInfo funStore = do
  -- 1. do Use analysis
  (useInfo1, clientstore) <- foldM fStore (useInfo, []) (_clientstore funStore)
  (useInfo2, serverstore) <- foldM fStore (useInfo, []) (_serverstore funStore)

  -- 2. Do deadcode elimination
  return (funStore {_clientstore=clientstore} {_serverstore=serverstore})

  where
    fStore (useInfo, store) (name, codeTypeCode) = do
      (useInfo1, codeTypeCode1) <- doCode useInfo codeTypeCode
      return (useInfo1, store++[(name,codeTypeCode1)])

doCode :: Monad m => UseInfo -> (CodeType, Code) -> m (UseInfo, (CodeType, Code))
doCode useInfo (CodeType as1 ls1 tys ty, Code ls2 as2 vs opencode) = do
  (useInfo1, opencode1) <- doOpenCode useInfo opencode ty
  return (useInfo1, (CodeType as1 ls1 tys ty, Code ls2 as2 vs opencode1))

doOpenCode :: Monad m => UseInfo -> OpenCode -> Type -> m (UseInfo, OpenCode)
doOpenCode useInfo (CodeAbs xTys expr) (FunType _ _ resty) = do
  (useInfo1, expr1) <- doExpr useInfo expr resty
  return (useInfo1, CodeAbs xTys expr1)
doOpenCode useInfo (CodeTypeAbs tyvars expr) (TypeAbsType _ bodyty) = do
  (useInfo1, expr1) <- doExpr useInfo expr bodyty
  return (useInfo1, CodeTypeAbs tyvars expr1)
doOpenCode useInfo (CodeLocAbs locvars expr) (LocAbsType _ bodyty) = do
  (useInfo1, expr1) <- doExpr useInfo expr bodyty
  return (useInfo1, CodeLocAbs locvars expr1)
