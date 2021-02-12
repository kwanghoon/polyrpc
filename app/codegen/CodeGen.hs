module CodeGen (codeGen) where

import Location
import Prim
import Literal
import CSType
import qualified CSExpr as CS

import qualified Runtime as R

import Control.Monad.State

-- | Fresh name generation

data NameState = NameState { varNames :: [String] }

initialNameState :: NameState
initialNameState = NameState { varNames = map ("cg$"++) nameList }
  where
    nameList = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State NameState a

evalNameGen :: NameGen a -> a
evalNameGen = flip evalState initialNameState

freshVar :: NameGen String
freshVar = do
  vvs <- gets varNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s { varNames = vs }
      return v
    _ -> error $ "[freshVar] This will never happen."


-- | Code generation

codeGen :: Monad m => CS.GlobalTypeInfo -> CS.FunctionStore -> CS.Expr -> m (R.FunctionStore, R.Expr)
codeGen t_gti funStore t_expr =
   return $ evalNameGen (do 
     clientFunMap <- compFunMap clientLocName (CS._clientstore funStore)
     serverFunMap <- compFunMap serverLocName (CS._serverstore funStore)
     let r_funStore = R.FunctionStore
                      { R._clientstore=clientFunMap
                      , R._serverstore=serverFunMap }
     (r_expr, ctx_expr) <- compExpr t_expr
     return (r_funStore, ctx_expr r_expr))

-- | Erasure contexts for type abstractions and type applications

type Context = R.Expr -> R.Expr  -- do x1<-E1; ... ; xk<-Ek [ ]

ctxID :: R.Expr -> R.Expr
ctxID x = x

--------------------------------------------------
-- | function map compilation to untyped code map
--------------------------------------------------

compFunMap :: String -> CS.FunctionMap -> NameGen R.FunctionMap
compFunMap myloc csFunMap = do compFunMap' myloc csFunMap
  where
    compFunMap' myloc csFunMap = do
      foldM (\ r_FunMap (f, (_, CS.Code locvars _ xs opencode)) -> do
        let fvvars = locvars ++ xs
        (ys, expr) <- codeAbsToPair myloc opencode
        return $ r_FunMap ++ [(f, R.Code fvvars (R.CodeAbs ys expr))] ) [] csFunMap

    codeAbsToPair myloc (CS.CodeAbs xTys@[(x,_)] expr) = do
      (r_expr, ctx_expr) <- compExpr expr
      return (map fst xTys, ctx_expr r_expr)
    codeAbsToPair myloc (CS.CodeAbs xTys expr) =
      error $ "compFunMap: not a single arg var: " ++ show (length xTys)
       
    codeAbsToPair myloc (CS.CodeLocAbs locvars@[locvar] expr) = do
      (r_expr, ctx_expr) <- compExpr expr
      return (locvars, ctx_expr r_expr)
    codeAbsToPair myloc (CS.CodeLocAbs locvars expr) =
      error $ "compFunMap: not a single loc var: " ++ show (length locvars)

-- | Expression

compExpr :: CS.Expr -> NameGen (R.Expr, Context)

compExpr (CS.ValExpr v) = compVal v

compExpr (CS.Let bindDecls expr) = do
  (r_binds, ctx_binds) <- compBindDecls bindDecls
  (r_expr, ctx_expr) <- compExpr expr
  return (R.Let r_binds r_expr, ctx_binds . ctx_expr)

compExpr (CS.Case v _ alts) = do
  (r_v, ctx_v) <- compVal v
  (r_alts, ctx_alts) <- compAlts alts
  return (R.Case r_v r_alts, ctx_v . ctx_alts)

compExpr (CS.App f _ arg) = do
  (r_f, ctx_f) <- compVal f
  (r_arg, ctx_arg) <- compVal arg
  return (R.App r_f r_arg, ctx_f . ctx_arg)

compExpr (CS.TypeApp f _ _) = do
  (r_f, ctx_f) <- compVal f
  xName <- freshVar
  return (R.Let [R.Binding False xName r_f] (R.UnitM (R.Var xName)), ctx_f)

compExpr (CS.LocApp f _ locs) = do
  (r_f, ctx_f) <- compVal f
  r_flocs <- foldM (\ r_f loc -> do
               let r_loc = compLoc loc
               return (R.App r_f r_loc)) r_f locs
  return (r_flocs, ctx_f)

compExpr (CS.Prim op locs _ args) = do
  let r_locs = map compLoc locs
  (r_args, ctx_args) <- compVals args
  return (R.Prim op r_locs r_args, ctx_args)


-- | value

compVal :: CS.Value -> NameGen (R.Expr, Context)

compVal (CS.Var x) = return (R.Var x, ctxID)

compVal (CS.Lit lit) = return (R.Lit lit, ctxID)

compVal (CS.Tuple vs) = do
  ( r_vs, ctx_vs ) <- compVals vs
  return (R.Tuple r_vs, ctx_vs)

compVal (CS.Constr c locs _ vs _) = do
  let r_locs = map compLoc locs
  ( r_vs, ctx_vs ) <- compVals vs
  return (R.Constr c (r_locs ++ r_vs), ctx_vs)

compVal (CS.Closure vs _ (CS.CodeName f locs _) recfs) = do
  let r_locs = map compLoc locs
  ( r_vs, ctx_vs ) <- compVals vs
  return (R.Closure (r_locs ++ r_vs) (R.CodeName f) recfs, ctx_vs)
  
compVal (CS.TypeAbs _ expr recfs) = do
  (r_expr, ctx_expr) <- compExpr expr
  xName <- freshVar
  return (R.Var xName, ctx_expr . \x -> R.BindM [R.Binding False xName r_expr] x)

compVal (CS.UnitM v) = do
  (r_v, ctx_v) <- compVal v
  return (ctx_v $ R.UnitM r_v, ctxID)

compVal (CS.BindM bindDecls expr) = do
  ( r_binds, ctx_binds) <- compBindDecls bindDecls
  (r_expr, ctx_expr) <- compExpr expr
  return (ctx_binds . ctx_expr $ R.BindM r_binds r_expr, ctxID)

compVal (CS.Req f _ arg) = do
  (r_f, ctx_f) <- compVal f
  (r_arg, ctx_arg) <- compVal arg
  return (ctx_f . ctx_arg $ R.Req r_f r_arg, ctxID)

compVal (CS.Call f _ arg) = do
  (r_f, ctx_f) <- compVal f
  (r_arg, ctx_arg) <- compVal arg
  return (ctx_f . ctx_arg $ R.Call r_f r_arg, ctxID)

compVal (CS.GenApp loc f _ arg) = do
  let r_loc = compLoc loc
  (r_f, ctx_f) <- compVal f
  (r_arg, ctx_arg) <- compVal arg
  return (ctx_f . ctx_arg $ R.GenApp r_loc r_f r_arg, ctxID)

--
compVals :: [CS.Value] -> NameGen ([R.Value], Context)
compVals vs = do
  foldM (\ (r_vs, ctx) v -> do
           (r_v, ctx_v) <- compVal v
           return ( r_vs ++ [r_v], ctx . ctx_v )) ([], ctxID) vs

-- | binding declaration
compBindDecls :: [CS.BindingDecl] -> NameGen ([R.BindingDecl], Context)
compBindDecls bindDecls = do
  foldM (\ (r_binds, ctx) bind -> do 
           (r_bind, ctx_bind) <- compBindDecl bind
           return ( r_binds ++ [r_bind], ctx . ctx_bind ))  ([], ctxID) bindDecls

compBindDecl :: CS.BindingDecl -> NameGen (R.BindingDecl, Context)
compBindDecl (CS.Binding b x _ expr) = do
  (r_expr, ctx) <- compExpr expr
  return (R.Binding b x r_expr, ctx)

-- | alternatives
compAlts :: [CS.Alternative] -> NameGen ([R.Alternative], Context)
compAlts alts = do
  foldM (\ (r_alts, ctx) alt -> do
           (r_alt, ctx_alt) <- compAlt alt
           return ( r_alts ++ [r_alt], ctx . ctx_alt )) ([], ctxID) alts

compAlt :: CS.Alternative -> NameGen (R.Alternative, Context)
compAlt (CS.Alternative c xs expr) = do
  (r_expr, ctx) <- compExpr expr
  return (R.Alternative c xs (ctx r_expr), ctxID)
  
compAlt (CS.TupleAlternative xs expr) = do
  (r_expr, ctx) <- compExpr expr
  return (R.TupleAlternative xs (ctx r_expr), ctxID)

-- | location
compLoc :: Location -> R.Value
compLoc (Location constloc) 
  | constloc == clientLocName = R.Constr clientLocName []
  | constloc == serverLocName = R.Constr serverLocName []
  | otherwise = error $ "cgLoc: not found: " ++ constloc

compLoc (LocVar x) = R.Var x
