module CodeGen where

import Location
import Prim
import Literal
import CSType
import qualified CSExpr as CS

import qualified Runtime as R

codeGen :: Monad m => CS.GlobalTypeInfo -> CS.FunctionStore -> CS.Expr -> m (R.FunctionStore, R.Expr)
codeGen t_gti funStore t_expr = do
   let clientFunMap = compFunMap clientLocName (CS._clientstore funStore)
   let serverFunMap = compFunMap serverLocName (CS._serverstore funStore)
   let r_funStore = R.FunctionStore { R._clientstore=clientFunMap, R._serverstore=serverFunMap }
   let r_expr = compExpr t_expr
   return (r_funStore, r_expr)

--------------------------------------------------
-- | function map compilation to untyped code map
--------------------------------------------------

compFunMap :: String -> CS.FunctionMap -> R.FunctionMap
compFunMap myloc csFunMap = funMap
  where
    funMap = compFunMap' myloc csFunMap

    compFunMap' myloc csFunMap =
      [ (f, R.Code fvvars (R.CodeAbs ys expr))
      | (f, (_, CS.Code locvars tyvars xs opencode)) <- csFunMap,
        let fvvars = locvars ++ xs,
        let (ys, expr) = codeAbsToPair myloc opencode
      ]

    codeAbsToPair myloc (CS.CodeAbs xTys@[(x,_)] expr) = (map fst xTys, compExpr expr)
    codeAbsToPair myloc (CS.CodeAbs xTys expr) =
      error $ "compFunMap: not a single arg var: " ++ show (length xTys)
       
    codeAbsToPair myloc (CS.CodeLocAbs locvars@[locvar] expr) = (locvars, compExpr expr)
    codeAbsToPair myloc (CS.CodeLocAbs locvars expr) =
      error $ "compFunMap: not a single loc var: " ++ show (length locvars)

compExpr :: CS.Expr -> R.Expr  -- Todo: Compiling Req/Call/GenApp, you will need the current loc.

compExpr (CS.ValExpr (CS.UnitM v)) = R.UnitM (compVal v)
compExpr (CS.ValExpr (CS.BindM bindDecls expr)) =
  R.BindM (map compBindDecl bindDecls) (compExpr expr)
  
compExpr (CS.ValExpr (CS.Req f _ arg)) = R.Req (compVal f) (compVal arg)
compExpr (CS.ValExpr (CS.Call f _ arg)) = R.Call (compVal f) (compVal arg)
compExpr (CS.ValExpr (CS.GenApp loc f _ arg)) = R.GenApp (compLoc loc) (compVal f) (compVal arg)
compExpr (CS.ValExpr v) = error $ "[codegen:compVal] ValExpr: Unexpected value: " ++ show v

compExpr (CS.Let bindDecls expr) = R.Let (map compBindDecl bindDecls) (compExpr expr)
compExpr (CS.Case v _ alts) = R.Case (compVal v) (map compAlt alts)
compExpr (CS.App f _ arg) = R.App (compVal f) (compVal arg)
compExpr (CS.TypeApp f _ _) = compVal f
compExpr (CS.LocApp f _ locs) = foldl (\ f v -> R.App f v) (compVal f) (map compLoc locs)
compExpr (CS.Prim op locs _ args) = R.Prim op (map compLoc locs) (map compVal args)

compVal :: CS.Value -> R.Expr
compVal (CS.Var x) = R.Var x
compVal (CS.Lit lit) = R.Lit lit
compVal (CS.Tuple vs) = R.Tuple (map compVal vs)
compVal (CS.Constr c locs _ vs _) = R.Constr c (map compLoc locs ++ map compVal vs)
compVal (CS.Closure vs _ (CS.CodeName f locs _) recfs) =
  R.Closure (map compLoc locs ++ map compVal vs) (R.CodeName f) recfs
  
compVal (CS.TypeAbs _ expr recfs) = compExpr expr

compVal v = error $ "[CodeGen:compVal] Unexpected value: " ++ show v

compBindDecl :: CS.BindingDecl -> R.BindingDecl
compBindDecl (CS.Binding b x _ expr) =
  R.Binding b x (compExpr expr)

compAlt :: CS.Alternative -> R.Alternative
compAlt (CS.Alternative c xs expr) = R.Alternative c xs (compExpr expr)
compAlt (CS.TupleAlternative xs expr) = R.TupleAlternative xs (compExpr expr)

compLoc :: Location -> R.Value
compLoc (Location constloc) 
  | constloc == clientLocName = R.Constr clientLocName []
  | constloc == serverLocName = R.Constr serverLocName []
  | otherwise = error $ "cgLoc: not found: " ++ constloc

compLoc (LocVar x) = R.Var x



