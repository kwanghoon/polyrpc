module CodeGen where

import Location
import Prim
import Literal
import CSType
import qualified CSExpr as CS

import qualified Runtime as R

codeGen :: Monad m => CS.GlobalTypeInfo -> CS.FunctionStore -> CS.Expr -> m ()
codeGen t_gti funStore t_expr = return ()

-- | function map compilation

cgFunMap :: String -> CS.FunctionMap -> R.FunctionMap
cgFunMap myloc csFunMap = funMap
  where
    funMap = cgFunMap' myloc csFunMap funMap

    cgFunMap' myloc csFunMap funMap =
      [ (f, R.Code fvvars (R.CodeAbs ys action))
      | (f, (_, CS.Code locvars tyvars xs opencode)) <- csFunMap,
        let fvvars = locvars ++ xs,
        let (ys, action) = codeAbsToPair myloc opencode
      ]

    codeAbsToPair myloc (CS.CodeAbs xTys@[(x,_)] expr) =
      let actionExpr = cgExpr myloc expr in
      (map fst xTys, \env v -> actionExpr funMap (env ++ [(x,v)]))
    codeAbsToPair myloc (CS.CodeAbs xTys expr) =
      error $ "cgFunMap: not a single arg var: " ++ show (length xTys)
       
    codeAbsToPair myloc (CS.CodeLocAbs locvars@[locvar] expr) =
      let actionExpr = cgExpr myloc expr in
      (locvars, \env v -> actionExpr funMap (env ++ [(locvar,v)]))
    codeAbsToPair myloc (CS.CodeLocAbs locvars expr) =
      error $ "cgFunMap: not a single loc var: " ++ show (length locvars)


-- | cgExpr

cgExpr :: String -> CS.Expr -> R.FunctionMap -> R.Env -> R.RuntimeM R.Value
       -- String ==> Location name

cgExpr myloc (CS.ValExpr (CS.UnitM v)) =
  let f = cgVal v
  in  (\ funMap env -> return $ f funMap env)

cgExpr myloc (CS.ValExpr (CS.BindM [CS.Binding _ x _ bexpr] expr)) =
  let actionBexpr = cgExpr myloc bexpr
      actionExpr = cgExpr myloc expr
  in  (\ funMap env -> do
           bvalue <- actionBexpr funMap env
           actionExpr funMap (env ++ [(x,bvalue)]) )

cgExpr myloc (CS.ValExpr (CS.BindM bindDecls expr)) =
  error $ "cgExpr: not a single binding in BindM: " ++ show (length bindDecls)
  
cgExpr myloc (CS.ValExpr (CS.Req f _ arg)) =
  let actionF = cgVal f
      actionArg = cgVal arg
  in  (\ funMap env -> do
          let _f   = actionF funMap env
          let _arg = actionArg funMap env
          R.req funMap _f _arg )
  
cgExpr myloc (CS.ValExpr (CS.Call f _ arg)) =
  let actionF = cgVal f
      actionArg = cgVal arg
  in  (\ funMap env -> do
          let _f = actionF funMap env
          let _arg = actionArg funMap env
          R.call funMap _f _arg )
  
cgExpr myloc (CS.ValExpr (CS.GenApp loc f _ arg)) =
  let actionF = cgVal f
      actionArg = cgVal arg
      actionLoc = cgLoc loc 
  in  (\ funMap env -> do
          let _f = actionF funMap env
          let _arg = actionArg funMap env
          let _loc = actionLoc env
  
          if myloc == clientLocName then
           case _loc of
               R.Constr fLoc [] ->
                 if myloc == fLoc then  R.apply funMap _f _arg
                 else R.req funMap _f _arg
               _ -> error $ "cgExpr: invalid location: " ++ show _loc
  
          else if myloc == serverLocName then
           case _loc of
               R.Constr fLoc [] ->
                 if myloc == fLoc then  R.apply funMap _f _arg
                 else R.call funMap _f _arg
               _ -> error $ "cgExpr: invalid location: " ++ show _loc
  
          else error $ "cgExpr: invalid location: " ++ myloc )

cgExpr myloc (CS.Let [CS.Binding _ x _ bexpr] expr) =
  let actionBexpr = cgExpr myloc bexpr
      actionExpr = cgExpr myloc expr
  in (\ funMap env -> do
          v <- actionBexpr funMap env
          actionExpr funMap (env ++ [(x, v)]) )

cgExpr myloc (CS.Let bindDecls expr) = 
  error $ "cgExpr: not a single binding in Let: " ++ show (length bindDecls)

cgExpr myloc (CS.Case v _ alts) =
  let actionV = cgVal v
      actionAlts = cgAlts myloc alts
  in  (\ funMap env -> do
           let _v = actionV funMap env
           actionCase _v actionAlts funMap env )
  where
    cgAlts myloc alts =
       [ case alt of
           CS.Alternative dname xs expr -> (Just dname, xs, cgExpr myloc expr)
           CS.TupleAlternative xs expr -> (Nothing, xs, cgExpr myloc expr)
       | alt <- alts ]

    actionCase v@(R.Constr cname args) actionAlts funMap env =
      case [(xs, actionExpr)
           | (Just dname, xs, actionExpr) <- actionAlts, cname==dname] of
        ((xs, actionExpr):_)
          | length args == length xs -> actionExpr funMap (env ++ zip xs args)
          | otherwise -> error $ "cgExpr: arity mismatch in an alternative: "
                           ++ show (length args) ++ " != " ++ show (length xs)
        [] -> error $ "cgExpr: No matching alternative for: " ++ show v

    actionCase (R.Tuple args) [(Nothing, xs, actionExpr)] funMap env
      | length args == length xs = actionExpr funMap (env ++ zip xs args)
      | otherwise = error $ "cgExpr: arity mismatch in a tuple alternative: "
                               ++ show (length args) ++ " != " ++ show (length xs)
       
    actionCase (R.Tuple args) _ funMap env =
      error $ "cgExpr: Not a single tuple alternative"
      
    actionCase v actionAlts funMap env =
      error $ "cgExpr: No matching alternative for: " ++ show v

cgExpr myloc (CS.App f _ arg) =
  let actionF = cgVal f
      actionArg = cgVal arg
  in  (\ funMap env -> do
          let _f = actionF funMap env
          let _arg = actionArg funMap env
          R.apply funMap _f _arg )
  
cgExpr myloc (CS.TypeApp f _ tyargs) =
  let actionF = cgVal f
  in  (\ funMap env -> do
          let _f = actionF funMap env
          return _f )

cgExpr myloc (CS.LocApp f _ locargs) =
  let actionF = cgVal f
      actionLocargs = map cgLoc locargs
  in  (\ funMap env -> do
           let _f = actionF funMap env
           let _locargs = map (\f -> f env) actionLocargs
           foldl (\ action locval -> do
                fval <- action
                R.apply funMap fval locval) (return _f) _locargs )

cgExpr myloc (CS.Prim op locargs _ args) =
  let actionLocargs = map cgLoc locargs
      actionArgs = map cgVal args
  in  (\ funMap env -> do
           let _locargs = map (\f -> f env) actionLocargs
           let _args = map (\f -> f funMap env) actionArgs
           R.prim op _locargs _args )

-- | cgVal

cgVal :: CS.Value -> R.FunctionMap -> R.Env -> R.Value
cgVal (CS.Var x) = \funMap env ->
  case [ v | (y,v) <- env, x==y ] of
    (v:_) -> v
    [] -> error $ "cgVal: not found: " ++ x

cgVal (CS.Lit lit) = \funMap env -> R.Lit lit

cgVal (CS.Tuple vs) =
  let fs = map cgVal vs in
  (\ funMap env -> let runtime_vs = map (\f -> f funMap env) fs in R.Tuple runtime_vs )
    

cgVal (CS.Constr c locargs _ args _) =
  let fs = map cgLoc locargs 
      gs = map cgVal args
  in (\ funMap env ->
          let runtime_vs = map (\f -> f env) fs
              runtime_ws = map (\g -> g funMap env) gs
          in  R.Constr c $ runtime_vs ++ runtime_ws )

cgVal (CS.Closure freevals _ (CS.CodeName f locs _) optrecf) =
  let fs = map cgVal freevals
      gs = map cgLoc locs
  in  (\ funMap env ->
           let runtime_vs = map (\f -> f funMap env) fs
               runtime_ws = map (\g -> g env) gs
           in  R.Closure (runtime_ws ++ runtime_vs) (R.CodeName f) optrecf ) -- Note: locvals first!!

-- | cgLoc

cgLoc :: Location -> R.Env -> R.Value

cgLoc (Location constloc) 
  | constloc == clientLocName = \env -> R.Constr clientLocName []
  | constloc == serverLocName = \env -> R.Constr serverLocName []
  | otherwise = error $ "cgLoc: not found: " ++ constloc

cgLoc (LocVar x) = \env ->
  case [ z | (y,z) <- env, x==y ] of
    (w:_) -> w
    [] -> error $ "cgLoc: not found: " ++ x


