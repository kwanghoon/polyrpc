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

compFunMap :: String -> CS.FunctionMap -> R.FunctionMap
compFunMap myloc csFunMap = funMap
  where
    funMap = compFunMap' myloc csFunMap funMap

    compFunMap' myloc csFunMap funMap =
      [ (f, R.Code fvvars (R.CodeAbs ys action))
      | (f, (_, CS.Code locvars tyvars xs opencode)) <- csFunMap,
        let fvvars = locvars ++ xs,
        let (ys, action) = codeAbsToPair myloc opencode
      ]

    codeAbsToPair myloc (CS.CodeAbs xTys@[(x,_)] expr) =
      (map fst xTys, \env v -> interp myloc funMap (env ++ [(x,v)]) expr)
    codeAbsToPair myloc (CS.CodeAbs xTys expr) =
      error $ "compFuNMap: not a single arg var: " ++ show (length xTys)
       
    codeAbsToPair myloc (CS.CodeLocAbs locvars@[locvar] expr) =
      (locvars, \env v -> interp myloc funMap (env ++ [(locvar,v)]) expr)
    codeAbsToPair myloc (CS.CodeLocAbs locvars expr) =
      error $ "compFuNMap: not a single loc var: " ++ show (length locvars)



-- | interp

interp :: String -> R.FunctionMap -> R.Env -> CS.Expr -> IO R.Value  -- String ==> Location name

interp myloc funMap env (CS.ValExpr (CS.UnitM v)) =
  return $ interpVal funMap env v
  
interp myloc funMap env (CS.ValExpr (CS.BindM [CS.Binding _ x _ bexpr] expr)) = do
  bvalue <- interp myloc funMap env bexpr
  interp myloc funMap (env ++ [(x,bvalue)]) expr

interp myloc funMap env (CS.ValExpr (CS.BindM bindDecls expr)) =
  error $ "interp: not a single binding in BindM: " ++ show (length bindDecls)
  
interp myloc funMap env (CS.ValExpr (CS.Req f _ arg)) = do
  let _f   = interpVal funMap env f
  let _arg = interpVal funMap env arg
  R.req funMap _f _arg
  
interp myloc funMap env (CS.ValExpr (CS.Call f _ arg)) = do
  let _f   = interpVal funMap env f
  let _arg = interpVal funMap env arg
  R.call funMap _f _arg

interp myloc funMap env (CS.ValExpr (CS.GenApp loc f _ arg)) = do
  let _loc = interpLoc env loc
  let _f   = interpVal funMap env f
  let _arg = interpVal funMap env arg
  if myloc == clientLocName then
    case _loc of
        R.Constr fLoc [] ->
          if myloc == fLoc then  R.apply funMap _f _arg
          else R.req funMap _f _arg
        _ -> error $ "interp: invalid location: " ++ show _loc
  
  else if myloc == serverLocName then
    case _loc of
        R.Constr fLoc [] ->
          if myloc == fLoc then  R.apply funMap _f _arg
          else R.call funMap _f _arg
        _ -> error $ "interp: invalid location: " ++ show _loc
  
  else error $ "interp: invalid location: " ++ myloc

interp myloc funMap env (CS.Let [CS.Binding _ x _ bexpr] expr) = do
  v <- interp myloc funMap env bexpr
  interp myloc funMap (env ++ [(x, v)]) expr

interp myloc funMap env (CS.Let bindDecls expr) = 
  error $ "interp: not a single binding in Let: " ++ show (length bindDecls)

interp myloc funMap env (CS.Case v _ alts) = do
  let _v = interpVal funMap env v
  case _v of
    R.Constr cname args ->
      case [ alt | alt@(CS.Alternative dname _ _) <- alts, cname==dname ] of
        [CS.Alternative _ xs aexpr]
          | length args == length xs -> interp myloc funMap (env ++ zip xs args) aexpr
          | otherwise -> error $ "interp: No matching alternative for: "
                            ++ cname ++ show (length args) ++ " != " ++ show (length xs)
        _ -> error $ "interp: No matching alternative for: " ++ cname

    R.Tuple args ->
      case alts of
        [CS.TupleAlternative xs aexpr]
          | length args == length xs -> interp myloc funMap (env ++ zip xs args) aexpr
          | otherwise -> error $ "interp: No matching tuple alternative: "
                            ++ show (length args) ++ " != " ++ show (length xs)
        _ -> error $ "interp: Must be TupleAlternative but not: " ++ show alts

    _ -> error $ "interp: Must be Constr but not: " ++ show v


interp myloc funMap env (CS.App f _ arg) = do
  let _f = interpVal funMap env f
  let _arg = interpVal funMap env arg
  R.apply funMap _f _arg
  
interp myloc funMap env (CS.TypeApp f _ tyargs) = do
  let _f = interpVal funMap env f
  return _f

interp myloc funMap env (CS.LocApp f _ locargs) = do
  let _f = interpVal funMap env f
  let _locargs = map (interpLoc env) locargs
  foldl (\ faction locval -> do
           fval <- faction
           R.apply funMap fval locval) (return _f) _locargs

interp myloc funMap env (CS.Prim op locargs _ args) = do
  let _locargs = map (interpLoc env) locargs
  let _args = map (interpVal funMap env) args
  R.prim op _locargs _args


-- | interpVal

interpVal :: R.FunctionMap -> R.Env -> CS.Value -> R.Value
interpVal funMap env (CS.Var x) =
  case [ v | (y,v) <- env, x==y ] of
    (v:_) -> v
    [] -> error $ "interpVal: not found: " ++ x

interpVal funMap env (CS.Lit lit) = R.Lit lit

interpVal funMap env (CS.Tuple vs) = R.Tuple (map (interpVal funMap env) vs)

interpVal funMap env (CS.Constr c locargs _ args _) =
  R.Constr c $ map (interpLoc env) locargs ++ map (interpVal funMap env) args

interpVal funMap env (CS.Closure freevals _ (CS.CodeName f locs _) optrecf) = 
  let _freevals = map (interpVal funMap env) freevals
      _locvals = map (interpLoc env) locs
  in  R.Closure (_locvals ++ _freevals) (R.CodeName f) optrecf


-- | interpLoc

interpLoc :: R.Env -> Location -> R.Value

interpLoc env (Location constloc)
  | constloc == clientLocName = R.Constr clientLocName []
  | constloc == serverLocName = R.Constr serverLocName []
  | otherwise = error $ "interpLoc: not found: " ++ constloc

interpLoc env (LocVar x) =
  case [ z | (y,z) <- env, x==y ] of
    (w:_) -> w
    [] -> error $ "interpLoc: not found: " ++ x


