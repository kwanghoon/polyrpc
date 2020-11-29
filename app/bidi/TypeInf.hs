module TypeInf(typeInf) where

import Data.Either
import Data.Maybe
import qualified Data.Set as S
import Data.Tuple.HT(mapFst, fst3, snd3, thd3)

import Control.Monad (replicateM, foldM)

import Location
import Type
import Literal
import Prim
import Expr
import BasicLib

import Naming
import NameGen
import Context
import Pretty

-- typeInf :: Monad m => [TopLevelDecl] -> m (GlobalTypeInfo, [TopLevelDecl])
typeInf :: Monad m => [TopLevelDecl] -> m ()
typeInf toplevelDecls = do
  -- 1. split
  (bindingDecls, userDatatypes) <- splitTopLevelDecls toplevelDecls

  let datatypeDecls = builtinDatatypes ++ userDatatypes

  -- 2. collect all types, builtin or user-defined ones
  typeInfo <- collectDataTypeDecls datatypeDecls

  -- 3. elaborate data types
  elab_datatypeDecls <- elabDataTypeDecls typeInfo datatypeDecls
  dataTypeInfo <- collectDataTypeInfo elab_datatypeDecls

  -- 4. elaborate constructor types
  conTypeInfo <- elabConTypeDecls elab_datatypeDecls

  -- 5. elaborate types declared in the bindings
  partial_elab_bindingDecls <- elabBindingTypes typeInfo [] [] bindingDecls

--------------------------------
-- for fully recursive bindings:
--------------------------------
  bindingTypeInfo <- bindingTypes partial_elab_bindingDecls

  -- 6. elaborate bindings
  let basicLibTypeInfo = [(x,ty) | (x,ty,expr)<-basicLib]

  let gti = GlobalTypeInfo
              { _typeInfo=typeInfo
              , _conTypeInfo=conTypeInfo
              , _dataTypeInfo=dataTypeInfo
-------------------------------
-- for fully recursive bindings
-------------------------------
--              , _bindingTypeInfo=basicLibTypeInfo ++ bindingTypeInfo }
              , _bindingTypeInfo=basicLibTypeInfo }

  -- let initEnv = (emptyEnv{_varEnv=_bindingTypeInfo gti ++ bindingTypeInfo})
  -- elab_bindingDecls <- elaborate gti initEnv clientLoc partial_elab_bindingDecls

  let initGamma = mempty >++ map (uncurry CVar) (_bindingTypeInfo gti ++ bindingTypeInfo)
  let (elab_bindingDecls) = evalNameGen $ bidi gti initGamma clientLoc partial_elab_bindingDecls

  -- 7. return elaborated data types and bindings
  -- let elab_toplevels = [ LibDeclTopLevel x ty | (x,ty) <- basicLibTypeInfo]
  --                      ++ [ DataTypeTopLevel dt | dt <- elab_datatypeDecls]
  --                      ++ [ BindingTopLevel bd | bd <- elab_bindingDecls]

  -- let gti1 = gti {_bindingTypeInfo=basicLibTypeInfo ++ bindingTypeInfo}

  -- return (gti1, elab_toplevels)
  return ()

----------------------------------------------------------------------------
-- 1. Split toplevel declarations into datatypes and bindings
----------------------------------------------------------------------------

splitTopLevelDecls :: Monad m =>
  [TopLevelDecl] -> m ([BindingDecl], [DataTypeDecl])
splitTopLevelDecls toplevelDecls = do
  bindingsDatatypeList <- mapM splitTopLevelDecl toplevelDecls
  let (bindings,datatypes) = unzip bindingsDatatypeList
  return (concat bindings, concat datatypes)

splitTopLevelDecl :: Monad m =>
  TopLevelDecl -> m ([BindingDecl], [DataTypeDecl])
splitTopLevelDecl (BindingTopLevel bindingDecl)   = return ([bindingDecl], [])
splitTopLevelDecl (DataTypeTopLevel datatypeDecl) = return ([], [datatypeDecl])


----------------------------------------------------------------------------
-- 2. Collect bultin types and user-defined datatyps
----------------------------------------------------------------------------

-- type TypeInfo = [(String, [String], [String])]

lookupTypeCon :: Monad m => TypeInfo -> String -> m ([String], [String])
lookupTypeCon typeInfo x = do
  let found = [(locvars,tyvars) | (name, locvars, tyvars) <- typeInfo, x==name]
  if found /= []
    then return (head found)
    else error $ "lookupConstr: Not found construct : " ++ x

builtinDatatypes :: [DataTypeDecl]
builtinDatatypes = [
    (DataType unitType   [] [] []), -- data Unit
    (DataType intType    [] [] []), -- data Int
    (DataType boolType   [] []      -- data Bool = { True | False }
      [ TypeCon trueLit  []
      , TypeCon falseLit [] ]),
    (DataType stringType [] [] []), -- data String
    (DataType refType ["l"] ["a"] [])  -- data Ref
  ]


collectDataTypeDecls :: Monad m => [DataTypeDecl] -> m TypeInfo
collectDataTypeDecls datatypeDecls = do
  let nameTyvarsPairList = map collectDataTypeDecl datatypeDecls
  return nameTyvarsPairList

collectDataTypeDecl (DataType name locvars tyvars typeConDecls) =
  if isTypeName name
     && and (map isLocationVarName locvars)
     && allUnique locvars == []
     && and (map isTypeVarName tyvars)
     && allUnique tyvars == []
  then (name, locvars, tyvars)
  else error $ "[TypeCheck] collectDataTypeDecls: Invalid datatype: "
                 ++ name ++ " " ++ show locvars++ " " ++ show tyvars

----------------------------------------------------------------------------
-- 3. Elaboration of datatype declarations
--  by elaborating Int as an identifier into ConType Int [],
--     checking duplicate type variables in each datatype declaration, and
--     checking duplicate constructor names in all datatype declarations.
----------------------------------------------------------------------------

elabDataTypeDecls :: Monad m => TypeInfo -> [DataTypeDecl] -> m [DataTypeDecl]
elabDataTypeDecls typeInfo datatypeDecls =
  mapM (elabDataTypeDecl typeInfo) datatypeDecls

elabDataTypeDecl :: Monad m => TypeInfo -> DataTypeDecl -> m DataTypeDecl
elabDataTypeDecl typeInfo (DataType name locvars tyvars typeConDecls) = do
  elab_typeConDecls <- mapM (elabTypeConDecl typeInfo locvars tyvars) typeConDecls
  return (DataType name locvars tyvars elab_typeConDecls)

elabTypeConDecl :: Monad m => TypeInfo -> [String] -> [String] -> TypeConDecl -> m TypeConDecl
elabTypeConDecl typeInfo locvars tyvars (TypeCon con tys) = do
  elab_tys <- mapM (elabType typeInfo tyvars locvars ) tys
  return (TypeCon con elab_tys)

----------------------------------------------------------------------------
-- 4. Elaboration of constructor types
----------------------------------------------------------------------------

-- type ConTypeInfo = [(String, ([Type], String, [String], [String]))]

-- lookupConstr :: GlobalTypeInfo -> String -> [([Type], String, [String], [String])]
-- lookupConstr gti x = [z | (con, z) <- _conTypeInfo gti, x==con]

elabConTypeDecls :: Monad m => [DataTypeDecl] -> m ConTypeInfo
elabConTypeDecls elab_datatypeDecls = do
  conTypeInfoList <- mapM elabConTypeDecl elab_datatypeDecls
  let conTypeInfo = concat conTypeInfoList
  case allUnique [con | (con,_) <- conTypeInfo] of
    [] -> return conTypeInfo
    (con:_) -> error $ "allConTypeDecls: duplicate constructor: " ++ con

elabConTypeDecl :: Monad m => DataTypeDecl -> m ConTypeInfo
elabConTypeDecl (DataType name locvars tyvars typeConDecls) = do
  return [ (con, (argtys, name, locvars, tyvars)) | TypeCon con argtys <- typeConDecls ]

----------------------------------------------------------------------------
-- 5. Elaboration of types declared in bindings
----------------------------------------------------------------------------

-- type BindingTypeInfo = [(String, Type)]

elabBindingTypes :: Monad m => TypeInfo -> [String] -> [String] -> [BindingDecl] -> m [BindingDecl]
elabBindingTypes typeInfo tyvars locvars bindingDecls =
  mapM (\(Binding istop f ty expr)-> do
           elab_ty <- elabType typeInfo tyvars locvars ty
           return (Binding istop f elab_ty expr)) bindingDecls

bindingTypes :: Monad m => [BindingDecl] -> m [(String,Type)]
bindingTypes partial_elab_bindingDecls =
  mapM (\(Binding _ f ty _) -> return (f,ty)) partial_elab_bindingDecls

----------------------------------------------------------------------------
-- 6. Elaboration of bindings
----------------------------------------------------------------------------

-- data GlobalTypeInfo = GlobalTypeInfo
--        { _typeInfo :: TypeInfo
--        , _conTypeInfo :: ConTypeInfo
--        , _dataTypeInfo :: DataTypeInfo
--        , _bindingTypeInfo :: BindingTypeInfo }

-- elaborate :: Monad m => GlobalTypeInfo -> Env -> Location -> [BindingDecl] -> m [BindingDecl]
-- elaborate gti env loc [] =  return []
-- elaborate gti env loc (bindingDecl@(Binding _ f ty _):bindingDecls) = do
--   let gti1 = gti {_bindingTypeInfo = (f,ty):_bindingTypeInfo gti}   -- for self-recursion
--   elab_bindingDecl <- elabBindingDecl gti1 env loc bindingDecl
--   elab_bindingDecls <- elaborate gti1 env loc bindingDecls
--   return (elab_bindingDecl:elab_bindingDecls)

-- elabBindingDecl :: Monad m => GlobalTypeInfo -> Env -> Location -> BindingDecl -> m BindingDecl
-- elabBindingDecl gti env loc (Binding istop name ty expr) = do -- ToDo: When name is recursive, expr must be lambda abstraction!
--   -- let env = emptyEnv{_varEnv=_bindingTypeInfo gti}
--   (elab_expr,elab_ty) <- elabExpr gti env loc expr
--   if equalType elab_ty ty
--   then return (Binding istop name ty elab_expr)
--   else error $ "[TypeCheck] elabBindingDecl: Incorrect types: " ++ name ++ "\n" ++ show elab_ty ++ "\n" ++ show ty

bidi :: GlobalTypeInfo -> Context -> Location -> [BindingDecl] -> NameGen (Context, [BindingDecl])
bidi gti gamma loc bindingDecls =  bidiBindingDecls gti gamma loc bindingDecls

bidiBindingDecls :: GlobalTypeInfo -> Context -> Location -> [BindingDecl] -> NameGen (Context, [BindingDecl])
bidiBindingDecls gti gamma loc [] =  return (gamma, [])
bidiBindingDecls gti gamma loc (bindingDecl@(Binding _ f ty _):bindingDecls) = do
  let gti1 = gti {_bindingTypeInfo = (f,ty):_bindingTypeInfo gti}   -- for self-recursion
  (gamma1, elab_bindingDecl) <- bidiBindingDecl gti1 gamma loc bindingDecl
  (gamma2, elab_bindingDecls) <- bidiBindingDecls gti1 gamma1 loc bindingDecls
  return (gamma2, elab_bindingDecl:elab_bindingDecls)

bidiBindingDecl :: GlobalTypeInfo -> Context -> Location -> BindingDecl -> NameGen (Context, BindingDecl)
bidiBindingDecl gti gamma loc (Binding istop name ty expr) = do -- ToDo: When name is recursive, expr must be lambda abstraction!
  (delta, expr') <- typecheckExpr gti gamma clientLoc expr ty
  return (delta, Binding istop name ty expr')  -- apply delta to expr'???

----------------------------------------------------------------------------
-- [Common] Elaboration of types
----------------------------------------------------------------------------
elabType :: Monad m => TypeInfo -> [String] -> [String] -> Type -> m Type
elabType typeInfo tyvars locvars (TypeVarType x) = do
  if elem x tyvars then return (TypeVarType x)
  else if isConstructorName x then
          do (_locvars, _tyvars) <- lookupTypeCon typeInfo x
             if _locvars ==[] && _tyvars == []
             then return (ConType x [] [])
             else error $ "[TypeCheck]: elabType: Invalid type constructor: " ++ x
       else
          error $ "[TypeCheck] elabType: Not found: " ++ x ++ " in " ++ show tyvars

elabType typeInfo tyvars locvars (TupleType tys) = do
  elab_tys <- mapM (elabType typeInfo tyvars locvars) tys
  return (TupleType elab_tys)

elabType typeInfo tyvars locvars (FunType ty1 (Location loc) ty2) = do
  elab_ty1 <- elabType typeInfo tyvars locvars ty1
  elab_ty2 <- elabType typeInfo tyvars locvars ty2
  let loc0 = if loc `elem` locvars
             then LocVar loc else Location loc
  return (FunType elab_ty1 loc0 elab_ty2)

elabType typeInfo tyvars locvars (FunType ty1 (LocVar _) ty2) =
  error $ "[TypeCheck] elabType: FunType: LocVar"

elabType typeInfo tyvars locvars (TypeAbsType abs_tyvars ty) = do
  elab_ty <- elabType typeInfo (abs_tyvars ++ tyvars) locvars ty
  return (TypeAbsType abs_tyvars elab_ty)

elabType typeInfo tyvars locvars (LocAbsType abs_locvars ty) = do
  elab_ty <- elabType typeInfo tyvars (abs_locvars ++ locvars) ty
  return (LocAbsType abs_locvars elab_ty)

elabType typeInfo tyvars locvars (ConType name locs tys) = do
  (_locvars, _tyvars) <- lookupTypeCon typeInfo name
  if length _locvars == length locs && length _tyvars == length tys
    then do elab_locs <- mapM (elabLocation locvars) locs
            elab_tys <- mapM (elabType typeInfo tyvars locvars) tys
            return (ConType name elab_locs elab_tys)
    else error $ "[TypeCheck]: elabType: Invalud args for ConType: " ++ name


elabLocation :: Monad m => [String] -> Location -> m Location
elabLocation locvars (Location loc)
  | loc `elem` locvars = return (LocVar loc)
  | otherwise = return (Location loc)
elabLocation locvars (LocVar x)
  | x `elem` locvars = return (LocVar x)
  | otherwise = error $ "[TypeCheck] elabLocation: Not found LocVar " ++ x

----------------------------------------------------------------------------
-- [Common] Elaboration of expressions
----------------------------------------------------------------------------

-- data Env = Env
--        { _locVarEnv  :: [String]
--        , _typeVarEnv :: [String]
--        , _varEnv     :: BindingTypeInfo }

emptyEnv = Env {_varEnv=[], _locVarEnv=[], _typeVarEnv=[]}

lookupVar :: Env -> String -> [Type]
lookupVar env x = [ty | (y,ty) <- _varEnv env, x==y]

lookupLocVar :: Env -> String -> Bool
lookupLocVar env x = elem x (_locVarEnv env)

lookupTypeVar :: Env -> String -> Bool
lookupTypeVar env x = elem x (_typeVarEnv env)

--
-- type DataTypeInfo = [(String, ([String], [(String,[Type])]))]

-- lookupDataTypeName gti x = [info | (y,info) <- _dataTypeInfo gti, x==y]

collectDataTypeInfo :: Monad m => [DataTypeDecl] -> m DataTypeInfo
collectDataTypeInfo datatypeDecls = do
  mapM get datatypeDecls
  where get (DataType name locvars tyvars tycondecls) =
          return (name, (locvars, tyvars,map f tycondecls))
        f (TypeCon s tys) = (s,tys)

--

-- For making constructor location/type/value functions
mkLocAbs loc cname tyname [] tyvars argtys = mkTypeAbs loc cname tyname [] tyvars argtys
mkLocAbs loc cname tyname locvars tyvars argtys =
  let (tyabs, tyabsTy) = mkTypeAbs loc cname tyname locvars tyvars argtys
  in  (singleLocAbs (LocAbs locvars tyabs)
      , singleLocAbsType (LocAbsType locvars tyabsTy))

mkTypeAbs loc cname tyname locvars [] argtys = mkAbs loc cname tyname locvars [] argtys
mkTypeAbs loc cname tyname locvars tyvars argtys =
  let (abs, absTy) = mkAbs loc cname tyname locvars tyvars argtys
  in  (singleTypeAbs (TypeAbs tyvars abs)
      , singleTypeAbsType (TypeAbsType tyvars absTy))

mkAbs loc cname tyname locvars tyvars [] =
  let locs = map LocVar locvars
      tys  = map TypeVarType tyvars
  in  (Constr cname locs tys [] [], ConType tyname locs tys)

mkAbs loc cname tyname locvars tyvars argtys =
  let locs = map LocVar locvars
      tys  = map TypeVarType tyvars
      varNames = take (length argtys) ["arg"++show i | i<- [1..]]
      vars = map Var varNames
      abslocs = loc : abslocs
      varTypeLocList = zip3 varNames (map Just argtys) abslocs
  in  (singleAbs (Abs varTypeLocList (Constr cname locs tys vars argtys))
      , foldr ( \ ty ty0 -> FunType ty loc ty0) (ConType tyname locs tys) argtys)

{-
elabExpr :: Monad m =>
  GlobalTypeInfo -> Env -> Location -> Expr -> m (Expr, Type)
elabExpr gti env loc (Var x)
  | isConstructorName x =    -- if it is a constructor
  case lookupConstr gti x  of
        ((argtys, tyname, locvars, tyvars):_) -> return $ mkLocAbs loc x tyname locvars tyvars argtys

        [] -> error $ "[TypeCheck] elabExpr: Not found constructor " ++ x

  | otherwise =    --  isBindingName x =        -- if it is a term variable
  case lookupVar env x of    -- try to find it in the local var env or
    (x_ty:_) -> return (Var x, x_ty)
    [] -> error $ "[TypeCheck] elabExpr: Not found variable " ++ x

elabExpr gti env loc (TypeAbs tyvars expr) = do
  let typeVarEnv = _typeVarEnv env
  let typeVarEnv' = reverse tyvars ++ typeVarEnv
  (elab_expr, elab_ty) <- elabExpr gti (env{_typeVarEnv=typeVarEnv'}) loc expr
  return (singleTypeAbs (TypeAbs tyvars elab_expr), singleTypeAbsType (TypeAbsType tyvars elab_ty))

elabExpr gti env loc (LocAbs locvars expr) = do
  let locVarEnv = _locVarEnv env
  let locVarEnv' = reverse locvars ++ locVarEnv
  (elab_expr, elab_ty) <- elabExpr gti (env{_locVarEnv=locVarEnv'}) loc expr
  return (singleLocAbs (LocAbs locvars elab_expr), singleLocAbsType (LocAbsType locvars elab_ty))

elabExpr gti env loc_0 (Abs [(var,Just argty,loc)] expr)  = do
  elab_argty <- elabType (_typeInfo gti) (_typeVarEnv env) (_locVarEnv env) argty
  elab_loc <- elabLocation (_locVarEnv env) loc
  let varEnv = _varEnv env
  let varEnv' = (var,elab_argty):varEnv
  (elab_expr, ret_ty) <- elabExpr gti (env{_varEnv=varEnv'}) elab_loc expr
  return (Abs [(var,Just elab_argty,elab_loc)] elab_expr, FunType elab_argty elab_loc ret_ty)

elabExpr gti env loc_0 (Abs ((var,Just argty,loc):varTypeLocList) expr)  = do
  elab_argty <- elabType (_typeInfo gti) (_typeVarEnv env) (_locVarEnv env) argty
  elab_loc <- elabLocation (_locVarEnv env) loc
  let varEnv = _varEnv env
  let varEnv' = (var,elab_argty):varEnv
  (elab_expr, ret_ty) <-
    elabExpr gti (env{_varEnv=varEnv'}) elab_loc (singleAbs (Abs varTypeLocList expr))
  return (Abs [(var,Just elab_argty,elab_loc)] elab_expr, FunType elab_argty elab_loc ret_ty)

elabExpr gti env loc_0 (Abs triple expr)  =
  error $ "[TypeCheck] elabExpr: Abs argument: empty triple or no annotated type" ++ show triple

elabExpr gti env loc (Let letBindingDecls expr) = do
  let typeInfo = _typeInfo gti
  partial_elab_letBindingDecls
     <- elabBindingTypes typeInfo (_typeVarEnv env) (_locVarEnv env) letBindingDecls

--------------------------------
-- for fully recursive bindings:
--------------------------------
--  letBindingTypeInfo <- bindingTypes partial_elab_letBindingDecls

--  let letBindingTypeInfo' = letBindingTypeInfo ++ _bindingTypeInfo gti
--  let gti1 = gti {_bindingTypeInfo=letBindingTypeInfo'}
  let gti1 = gti
  elab_letBindingDecls <- elaborate gti1 env loc partial_elab_letBindingDecls

  letBindingTypeInfo <- bindingTypes partial_elab_letBindingDecls -- for let body

  let varEnv' = letBindingTypeInfo ++ _varEnv env
  (elab_expr, elab_ty) <- elabExpr gti (env {_varEnv=varEnv'}) loc expr
  return (Let elab_letBindingDecls elab_expr, elab_ty)

elabExpr gti env loc (Case expr _ []) =
  error $ "[TypeCheck] empty alternatives"

elabExpr gti env loc (Case expr _ alts) = do
  (elab_caseexpr, casety) <- elabExpr gti env loc expr
  case casety of
    ConType tyconName locs tys ->
      case lookupDataTypeName gti tyconName of
        ((locvars, tyvars, tycondecls):_) -> do
          (elab_alts, altty) <- elabAlts gti env loc locs locvars tys tyvars tycondecls alts
          return (Case elab_caseexpr (Just casety) elab_alts, altty)
        [] -> error $ "[TypeCheck] elabExpr: invalid constructor type: " ++ tyconName

    TupleType tys -> do
      (elab_alts, altty) <- elabAlts gti env loc [] [] tys [] [] alts
      return (Case elab_caseexpr (Just casety) elab_alts, altty)

    _ -> error $ "[TypeCheck] elabExpr: case expr not constructor type"

elabExpr gti env loc (App left_expr maybe right_expr l) = do
  (elab_left_expr, left_ty) <- elabExpr gti env loc left_expr
  (elab_right_expr, right_ty) <- elabExpr gti env loc right_expr
  case left_ty of
    FunType argty loc0 retty ->
      if equalType argty right_ty
      then return (App elab_left_expr (Just left_ty) elab_right_expr (Just loc0), retty)
      else error $ "[TypeCheck] elabExpr: not equal arg type in app:\n"
                   ++ show (App left_expr maybe right_expr l) ++ "\n" ++ show argty ++ "\n" ++ show right_ty
    _ -> error $ "[TypeCheck] elabExpr: not function type in app:\n"
                   ++ show (App left_expr maybe right_expr l) ++ "\n" ++ show left_ty ++ "\n" ++ show right_ty

elabExpr gti env loc (TypeApp expr maybe tys) = do
  elab_tys <- mapM (elabType (_typeInfo gti) (_typeVarEnv env) (_locVarEnv env)) tys
  (elab_expr, elab_ty) <- elabExpr gti env loc expr
  case elab_ty of
    TypeAbsType tyvars ty0 ->
      if length tyvars == length elab_tys
      then return (singleTypeApp (TypeApp elab_expr (Just elab_ty) elab_tys), doSubst (zip tyvars elab_tys) ty0)
      else error $ "[TypeCheck] elabExpr: not equal length of arg types in type app: "
    _ -> error $ "[TypeCheck] elabExpr: not type-abstraction type in type app: " ++ "\n"
                   ++ show elab_ty ++ "\n"
                   ++ show (TypeApp expr maybe tys) ++ "\n"

elabExpr gti env loc (LocApp expr maybe locs) =
  let f (Location loc0) = if loc0 `elem` (_locVarEnv env) then LocVar loc0 else Location loc0
      f (LocVar x)      = error $ "[TypeCheck] elabExpr: LocApp: LocVar: " ++ x
  in do
  let locs0 = map f locs
  (elab_expr, elab_ty) <- elabExpr gti env loc expr
  case elab_ty of
    LocAbsType locvars ty0 ->
      if length locvars == length locs
      then return (singleLocApp (LocApp elab_expr (Just elab_ty) locs0), doSubstLoc (zip locvars locs0) ty0)
      else error $ "[TypeCheck] elabExpr: not equal length of arg locations in location app: " ++ show locvars ++ " " ++ show locs
    _ -> error $ "[TypeCheck] elabExpr: not location-abstraction type in type app: "

elabExpr gti env loc (Tuple exprs) = do
  elabExprTyList <- mapM (elabExpr gti env loc) exprs
  let (elab_exprs, tys) = unzip elabExprTyList
  return (Tuple elab_exprs, TupleType tys)

elabExpr gti env loc (Prim op op_locs@[] op_tys@[] exprs) =  -- A hack for the primitives with the current loc!
  elabExpr gti env loc (Prim op [loc] op_tys exprs)

elabExpr gti env loc (Prim op op_locs op_tys exprs) = do
  elab_op_locs <- mapM (elabLocation (_locVarEnv env)) op_locs
  elab_op_tys  <- mapM (elabType (_typeInfo gti) (_typeVarEnv env) (_locVarEnv env)) op_tys
  elabExprTyList <- mapM (elabExpr gti env loc) exprs
  let (elab_exprs, tys) = unzip elabExprTyList
  case op of
    EqIntPrimOp -> overloaded elab_op_locs elab_op_tys elab_exprs tys
    _           -> do
       match <- nonoverloaded elab_op_locs elab_op_tys elab_exprs tys op
       case match of
         Left expr -> return expr
         Right err -> error err

  where {- A hack: overloaded operator (=) : EqStringPrimOp, EqBoolPrimOp, EqIntPrimOp -}
     overloaded elab_op_locs elab_op_tys elab_exprs tys  = do
       matchInt <- nonoverloaded elab_op_locs elab_op_tys elab_exprs tys EqIntPrimOp
       case matchInt of
         Left expr -> return expr
         Right err -> do
            matchBool <- nonoverloaded elab_op_locs elab_op_tys elab_exprs tys EqBoolPrimOp
            case matchBool of
              Left expr -> return expr
              Right err -> do
                matchString <- nonoverloaded elab_op_locs elab_op_tys elab_exprs tys EqStringPrimOp
                case matchString of
                  Left expr -> return expr
                  Right err -> error $ err

     nonoverloaded elab_op_locs elab_op_tys elab_exprs tys  op =
       case lookupPrimOpType op of
         ((locvars, tyvars, argtys, retty):_) -> do
           let substTy  = zip tyvars op_tys
           let substLoc = zip locvars op_locs
           let substed_argtys = map (doSubstLoc substLoc . doSubst substTy) argtys

           if length tys==length argtys
              && and (map (uncurry equalType) (zip substed_argtys tys))
              && length locvars==length op_locs
              && length tyvars==length op_tys

           then return $ Left $ (Prim op elab_op_locs elab_op_tys elab_exprs, retty)

           else return $ Right $ "[TypeCheck] elabExpr: incorrect arg types in Prim op: "
                                  ++ show tys ++ " != " ++ show substed_argtys

         [] -> return $ Right $ "[TypeCheck] elabExpr: type not found type in Prim op: "
                                  ++ show op

elabExpr gti env loc (Lit literal) = return (Lit literal, typeOfLiteral literal)

elabExpr gti env loc (Constr conname locs contys exprs _argtys) = do
  elab_locs <- mapM (elabLocation (_locVarEnv env)) locs
  elab_contys <- mapM (elabType (_typeInfo gti) (_typeVarEnv env) (_locVarEnv env)) contys
  elabExprTyList <- mapM (elabExpr gti env loc) exprs
  let (elab_exprs, elab_tys) = unzip elabExprTyList
  case lookupConstr gti conname of
    ((argtys,tyname,locvars,tyvars):_) ->
      case (unifyTypes argtys elab_tys) of
        (Just subst) ->
          return (Constr conname elab_locs elab_contys elab_exprs            -- BUG: subt0???
                   (map (doSubst subst) elab_tys)
                 , doSubst subst (ConType tyname (map LocVar locvars) (map TypeVarType tyvars)))
        (Nothing) -> error $ "[TypeCheck] elabExpr: constructor arg types incorrect: " ++ conname

    [] -> error $ "[TypeCheck] elabExpr: constructor not found: " ++ conname

-- elabExpr gti env loc expr = error $ "[TypeCheck] elabExpr: " ++ show expr

--
elabAlts gti env loc locs locvars tys tyvars tycondecls [alt] = do
  let substLoc = zip locvars locs
  let substTy = zip tyvars tys
  (elab_alt, elab_ty) <- elabAlt gti env loc substLoc substTy tycondecls tys alt
  return ([elab_alt], elab_ty)

elabAlts gti env loc locs locvars tys tyvars tycondecls (alt:alts) = do
  let substLoc = zip locvars locs
  let substTy = zip tyvars tys
  (elab_alt, elab_ty1)  <- elabAlt gti env loc substLoc substTy tycondecls tys alt
  (elab_alts, elab_ty2) <- elabAlts gti env loc locs locvars tys tyvars tycondecls alts
  if equalType elab_ty1 elab_ty2
  then return (elab_alt:elab_alts, elab_ty1)
  else error $ "[TypeCheck] elabAlts: not equal alt type: " ++
                             (case alt of {
                               Alternative con args _ -> con ++ show args;
                               TupleAlternative args _ -> show args })

-- lookupCon tycondecls con =
--  [tys | (conname, tys) <- tycondecls, con==conname]

elabAlt gti env loc substLoc substTy tycondecls externTys (Alternative con args expr) = do
-- externTys only for TupleAlternative
  case lookupCon tycondecls con of
    (tys:_) ->
      if length tys==length args
      then do let tys' = map (doSubst substTy) (map (doSubstLoc substLoc) tys)
              let varEnv = _varEnv env
              let varEnv' = zip args tys' ++ varEnv
              (elab_expr, elab_ty) <- elabExpr gti (env {_varEnv=varEnv'}) loc expr
              return (Alternative con args elab_expr, elab_ty)
      else error $ "[TypeCheck] elabAlt: invalid arg length: " ++ con ++ show args

    [] -> error $ "[TypeCheck] elabAlt: constructor not found"

elabAlt gti env loc substLoc substTy tycondecls externTys (TupleAlternative args expr) = do
-- substTy==[], tycondecls==[]
  let varEnv  = _varEnv env
  let varEnv' = zip args externTys ++ varEnv
  (elab_expr, elab_ty) <- elabExpr gti (env {_varEnv=varEnv'}) loc expr
  return (TupleAlternative args elab_expr, elab_ty)
-}

----------------------------------------------------------------------------
-- Common Utils
----------------------------------------------------------------------------
allUnique [] = []
allUnique (x:xs) =
  if elem x xs then [x] else allUnique xs

----------------------------------------------------------------------------
-- For bidirectional typechecking
----------------------------------------------------------------------------

-- | Algorithmic sublocation:
subloc :: Context -> Location -> Location -> NameGen Context
subloc gamma loc1 loc2 =
  traceNS "subloc" (gamma, loc1, loc2) $
  checkwfloc gamma loc1 $ checkwfloc gamma loc2 $
    case (loc1, loc2) of
    -- <:Loc
    (Location c1, Location c2) | c1 == c2 -> return gamma

    (LocVar l1, LocVar l2)
      | (not (clExists l1)) && (not (clExists l2)) && l1 == l2 -> return gamma
      | clExists l1 && clExists l2 && l1 == l2 -> return gamma
      | otherwise ->
         error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    (LocVar l, loc)
      | clExists l && l `S.notMember` freeLVarsIn loc ->
          instantiateLocL gamma l loc
      | otherwise ->
         error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    (loc, LocVar l)
      | clExists l && l `S.notMember` freeLVarsIn loc ->
          instantiateLocR gamma loc l
      | otherwise ->
         error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    _ -> error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)


-- | Algorithmic instantiation location (left):
--   instantiateLocL Γ l loc = Δ <=> Γ |- l^ :=< loc -| Δ
instantiateLocL gamma l loc
  | clExists l =
    traceNS "instantiateLocL" (gamma, l, loc) $
    checkwfloc gamma loc $ checkwfloc gamma (LocVar l) $
    case lsolve gamma l loc of
    -- InstLSolve
    Just gamma' -> return gamma'
    Nothing -> case loc of
      -- InstLReach
      LocVar l'
        | clExists l' ->
            if lordered gamma l l' then
               return $ fromJust $ lsolve gamma l' (LocVar l)
            else
               return $ fromJust $ lsolve gamma l (LocVar l')
        | otherwise ->
            error $ "instantiateLocL: not ended with ^: " ++ l'
      _ -> error $ "The impossible happened! instantiateLocL: "
                ++ pretty (gamma, l, loc)

  | otherwise =
    error $ "instantiateLocL: not ended with ^: " ++ l


-- | Algorithmic instantiation location (right):
--   instantiateLocR Γ loc l = Δ <=> Γ |- loc =:< l -| Δ
instantiateLocR gamma loc l
  | clExists l =
    traceNS "instantiateLocR" (gamma, loc, l) $
    checkwfloc gamma loc $ checkwfloc gamma (LocVar l) $
    case lsolve gamma l loc of
      Just gamma' -> return gamma'
      Nothing -> case loc of
        -- InstRReach
        LocVar l'
          | clExists l' ->
             if lordered gamma l l' then
                return $ fromJust $ lsolve gamma l' (LocVar l)
             else
                return $ fromJust $ lsolve gamma l (LocVar l')
          | otherwise ->
              error $ "instantiateLocR: not ended with ^: " ++ l'

        _ -> error $ "The impossible happened! instantiateLocR: "
                  ++ pretty (gamma, loc, l)

  | otherwise =
    error $ "instantiateLocR: not ended with ^: " ++ l

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Context -> Type -> Type -> NameGen Context
subtype gamma typ1 typ2 =
  traceNS "subtype" (gamma, typ1, typ2) $
  checkwftype gamma typ1 $ checkwftype gamma typ2 $
    case (typ1, typ2) of
    -- <:Var
    (TypeVarType alpha, TypeVarType alpha')
      | not (cExists alpha) && not (cExists alpha')
          && alpha == alpha' -> return gamma
      | cExists alpha && cExists alpha'
          && alpha == alpha' && alpha `elem` existentials gamma -> return gamma
      | otherwise ->
          error $ "subtype(TypeVarType,TypeVarType), don't know what to do with: "
                         ++ pretty (gamma, typ1, typ2)

    (TypeVarType alpha, a)
      | cExists alpha
          && alpha `elem` existentials gamma
          && alpha `S.notMember` freeTVars a -> instantiateL gamma alpha a

    (a, TypeVarType alpha)
      | cExists alpha
          && alpha `elem` existentials gamma
          && alpha `S.notMember` freeTVars a -> instantiateR gamma a alpha

    -- <:TupleType
    (TupleType tys1, TupleType tys2)
      | length tys1 == length tys2 ->
         foldM (\ g (maybety1,maybety2) ->
                  case (maybety1, maybety2) of
                    (Just ty1, Just ty2) -> subtype g ty1 ty2
                    _ -> error $ "subtype: TupleType: not monotype: "
                                    ++ pretty (gamma, typ1, typ2))
           gamma (zip (map monotype tys1) (map monotype tys2))

    -- <:->
    (FunType a1 loc1 a2, FunType b1 loc2 b2) -> do
      theta <- subtype gamma b1 a1
      delta <- subtype theta (apply theta a2) (apply theta b2)
      subloc delta (lapply delta loc1) (lapply delta loc2)

    -- <:forallR
    (a, TypeAbsType alphas b) -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- replicateM (length alphas) freshTypeVar
      dropMarker (CForall (head alphas')) <$>
        subtype (gamma >++ map CForall alphas') a
           (typeSubsts (map TypeVarType alphas') alphas b)

    -- <:forallL
    (TypeAbsType alphas a, b) -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- replicateM (length alphas) freshExistsTypeVar
      dropMarker (CMarker (head alphas')) <$>
        subtype (gamma >++ map CMarker alphas' >++ map CExists alphas')
                (typeSubsts (map TypeVarType alphas') alphas a)
                b

    -- forallLoc
    (LocAbsType locvars1 a, LocAbsType locvars2 b)
      | locvars1 == locvars2 -> subtype gamma a b
      | length locvars1 == length locvars2 -> do
         locvars <- replicateM (length locvars1) freshLocationVar
         dropMarker (CLMarker (head locvars)) <$>
           subtype (gamma >++ map CLMarker locvars)
                   (locSubsts (map LocVar locvars) locvars1 a)
                   (locSubsts (map LocVar locvars) locvars2 a)
      | otherwise ->
         error $ "subtype: different length of location vars: "
                           ++ pretty (gamma, typ1, typ2)

    -- <:ConType
    (ConType c1 locs1 tys1, ConType c2 locs2 tys2)
      | c1 /= c2 || length locs1 /= length locs2 || length tys1 /= length tys2 ->
          error $ "subtype: ConType: different type constructors: "
                  ++ pretty (gamma, typ1, typ2)
      | otherwise -> do
          delta <- foldM (\ g (loc1, loc2) -> subloc g loc1 loc2) gamma (zip locs1 locs2)
          foldM (\ g (maybety1, maybety2) ->
                   case (maybety1, maybety2) of
                     (Just ty1, Just ty2) -> subtype g ty1 ty2
                     _ -> error $ "subtype: ConType: not monotype: "
                                     ++ pretty (gamma, typ1, typ2))
            gamma (zip (map monotype tys1) (map monotype tys2))

    _ -> error $ "subtype, don't know what to do with: "
                           ++ pretty (gamma, typ1, typ2)


-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Context -> TypeVar -> Type -> NameGen Context
instantiateL gamma alpha a
  | cExists alpha = instantiateL_ gamma alpha a
  | otherwise = error $ "instantiateL: not ended with ^: " ++ alpha

instantiateL_ gamma alpha a =
  traceNS "instantiateL" (gamma, alpha, a) $
  checkwftype gamma a $ checkwftype gamma (TypeVarType alpha) $
  case solve gamma alpha =<< monotype a of
    -- InstLSolve
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstLReach
      TypeVarType beta
        | not (cExists beta) ->
            error $ "instantiateL: InstLReach: not ended with ^: " ++ beta
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TypeVarType alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TypeVarType beta)

      -- InstLArr
      FunType a1 loc a2   -> do
        alpha1 <- freshExistsTypeVar
        alpha2 <- freshExistsTypeVar
        l      <- freshExistsLocationVar
        theta <- instantiateR (insertAt gamma (CExists alpha) $ context
                                [ CLExists l
                                , CExists alpha2
                                , CExists alpha1
                                , CExistsSolved alpha $ FunType (TypeVarType alpha1)
                                                                (LocVar l)
                                                                (TypeVarType alpha2)
                                ])
                              a1 alpha1
        delta <- instantiateL theta alpha2 (apply theta a2)
        instantiateLocL delta l (lapply delta loc)

      -- InstLAIIR
      TypeAbsType betas b -> do
        -- Do alpha conversion to avoid clashes
        betas' <- replicateM (length betas) freshTypeVar
        dropMarker (CForall (head betas')) <$> -- Todo: Ensure that betas is not null!
          instantiateL (gamma >++ map CForall betas')
                       alpha
                       (typeSubsts (map TypeVarType betas') betas b)

      -- Note: No polymorphic (location) abstraction is allowed.

      -- InstLAIIL
      -- LocAbsType locs b -> do  -- Should not be allowed!!

      -- Note: TupleType and ConType should be monomorphic types that
      --       will be handled above.

      -- InstLTupleType
      -- TupleType tys -> do
      --   alphas <- replicateM (length tys) freshExistsTypeVar
      --   foldM (\gamma (alphai, ai) ->
      --            instantiateL gamma alphai (apply gamma ai))
      --          (gamma >++ map CExists alphas
      --                 >++ [CExistsSolved alpha (TupleType (map TypeVarType alphas))])
      --          (zip alphas tys)

      -- InstLConstr
      -- ConType c locs tys -> do
      --   error "instantiateL: ConType: Not implemented"


      _ -> error $ "The impossible happened! instantiateL: "
                ++ pretty (gamma, alpha, a)


-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Context -> Type -> TypeVar -> NameGen Context
instantiateR gamma a alpha
  | cExists alpha = instantiateR_ gamma a alpha
  | otherwise = error $ "instantiateR: not ended with ^: " ++ alpha

instantiateR_ gamma a alpha =
  traceNS "instantiateR" (gamma, a, alpha) $
  checkwftype gamma a $ checkwftype gamma (TypeVarType alpha) $
  case solve gamma alpha =<< monotype a of
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstRReach
      TypeVarType beta
        | not (cExists beta) ->
            error $ "instantiateR: InstRReach: not ended with ^: " ++ beta
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TypeVarType alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TypeVarType beta)

      -- InstRArr
      FunType a1 loc a2   -> do
        alpha1 <- freshExistsTypeVar
        alpha2 <- freshExistsTypeVar
        l      <- freshExistsLocationVar
        theta <- instantiateL (insertAt gamma (CExists alpha) $ context
                                 [ CLExists l
                                 , CExists alpha2
                                 , CExists alpha1
                                 , CExistsSolved alpha $ FunType (TypeVarType alpha1)
                                                                 (LocVar l)
                                                                 (TypeVarType alpha2)
                                 ])
                              alpha1 a1
        delta <- instantiateR theta (apply theta a2) alpha2
        instantiateLocR delta (lapply delta loc) l

      -- InstRAIIL
      TypeAbsType betas b -> do
        -- Do alpha conversion to avoid clashes
        betas' <- replicateM (length betas) freshTypeVar
        dropMarker (CMarker (head betas')) <$>
          instantiateR (gamma >++ map CMarker betas' >++ map CExists betas')
                       (typeSubsts (map TypeVarType betas') betas b)
                       alpha

      -- Note: No polymorphic (location) abstraction is allowed.

      -- InstLAIIR
      -- LocAbsType locs b -> do  -- Should not be allowed!!

      -- Note: TupleType and ConType should be monomorphic types that
      --       will be handled above.

      -- InstRTupleType
      -- TupleType tys -> do
      --   alphas <- replicateM (length tys) freshExistsTypeVar
      --   foldM (\gamma (alphai, ai) ->
      --            instantiateR gamma (apply gamma ai) alphai)
      --          (gamma >++ map CExists alphas
      --                 >++ [CExistsSolved alpha (TupleType (map TypeVarType alphas))])
      --          (zip alphas tys)

      -- InstRConstr
      -- ConType c locs tys -> do
      --   error "instantiateR: ConType: Not implemented"

      _ -> error $ "The impossible happened! instantiateR: "
                ++ pretty (gamma, a, alpha)


-- | Type checking:
--   typecheck Γ loc e A = Δ <=> Γ |-_loc e <= A -| Δ
typecheckExpr :: GlobalTypeInfo -> Context -> Location -> Expr -> Type -> NameGen (Context, Expr)
typecheckExpr gti gamma loc expr typ =
  traceNS "typecheck" (gamma, loc, expr, typ) $ checkwftype gamma typ $
  typecheckExpr_ gti gamma loc expr typ

typecheckExpr_ :: GlobalTypeInfo -> Context -> Location -> Expr -> Type -> NameGen (Context, Expr)

-- ForallI
typecheckExpr_ gti gamma loc e (TypeAbsType alphas a) = do
  -- Do alpha conversion to avoid clashes
  alphas' <- replicateM (length alphas) freshTypeVar
  (gamma', e') <- mapFst (dropMarker (CForall (head alphas'))) <$>
       typecheckExpr gti (gamma >++ map CForall alphas') loc e
          (typeSubsts (map TypeVarType alphas') alphas a)
  return (gamma', TypeAbs alphas' e')

-- LForallI
typecheckExpr_ gti gamma loc (LocAbs ls0 e) (LocAbsType ls1 a) = do
  ls' <- replicateM (length ls0) freshLocationVar
  (gamma', e') <- mapFst (dropMarker (CLForall (head ls'))) <$>
        typecheckExpr gti (gamma >++ map CLForall ls') loc
          (locExprSubsts (map LocVar ls') ls0 e) (locSubsts (map LocVar ls') ls1 a)
  return (gamma', LocAbs ls' e')

-- ->I
typecheckExpr_ gti gamma loc (Abs [] e) a = do
  typecheckExpr_ gti gamma loc e a

typecheckExpr_ gti gamma loc (Abs [(x,mty,loc0)] e) (FunType a loc' b) = do
  x' <- freshVar
  gamma0 <- subloc gamma loc' loc0
  (gamma1, e') <- mapFst (dropMarker (CVar x' a)) <$>
        typecheckExpr_ gti (gamma0 >: CVar x' a) loc0 (subst (Var x') x e) b
  return (gamma1, Abs [(x,mty, loc0)] e')

typecheckExpr_ gti gamma loc (Abs ((x,mty,loc0):xmtyls) e) (FunType a loc' b) = do
  x' <- freshVar
  gamma0 <- subloc gamma loc' loc0
  (gamma1, e') <- mapFst (dropMarker (CVar x' a)) <$>
      typecheckExpr_ gti (gamma0 >: CVar x' a) loc0 (subst (Var x') x (Abs xmtyls e)) b
  return (gamma1, Abs [(x,mty,loc0)] e')

-- Sub
typecheckExpr_ gti gamma loc e b = do
  (a, theta, e') <- typesynthExpr gti gamma loc e
  delta <- subtype theta (apply theta a) (apply theta b)
  return (delta, e')

-- typecheckExpr_ gti gamma loc e typ = do
--   error $ "typecheckExpr: not implemented yet"


-- | Type synthesising:
--   typesynth Γ loc e = (A, Δ) <=> Γ |- e => A -| Δ
typesynthExpr :: GlobalTypeInfo -> Context -> Location -> Expr -> NameGen (Type, Context, Expr)
typesynthExpr gti gamma loc expr =
  traceNS "typesynth" (gamma, loc, expr) $ checkwf gamma $
  typesynthExpr_ gti gamma loc expr

-- Var
-- typesynthExpr_ gti gamma loc expr@(Var x) = do
--   return
--    ( fromMaybe (error $ "typesynth: not in scope " ++ pretty (expr, gamma))
--                (findVarType gamma x)
--    , gamma
--    , expr
--    )

typesynthExpr_ gti gamma loc expr@(Var x)
  | isConstructorName x =
      case lookupConstr gti x  of
        ((argtys, tyname, locvars, tyvars):_)
           -> do let (e', ty') = mkLocAbs loc x tyname locvars tyvars argtys
                 return (ty', gamma, e')

        [] -> error $ "[TypeInf] typesynthExpr: Not found constructor " ++ x

  | otherwise =
      return
       ( fromMaybe (error $ "typesynth: not in scope " ++ pretty (expr, gamma))
                   (findVarType gamma x)
       , gamma
       , expr
       )

-- Anno
-- typesynthExpr_ gti gamma loc expr@(EAnno e a) = do
--   (delta, e') <- typecheck gamma loc e a
--   return (a, delta, e')

-- ->I=> Original rule
typesynthExpr_ gti gamma loc expr@(Abs xmtyls e) = do
  xs'    <- replicateM (length xmtyls) freshVar
  alphas <- replicateM (length xmtyls) freshExistsTypeVar
  beta   <- freshExistsTypeVar
  let locs = map thd3 xmtyls
  let xs = map fst3 xmtyls
  (gamma', e') <- mapFst (dropMarker (CVar (last xs') (TypeVarType (last alphas)))) <$>
     typecheckExpr gti
       (gamma >++ map CExists alphas
              >++ [CExists beta]
              >++ map (uncurry CVar)
                      (zip xs' (map TypeVarType alphas)))
                     (last locs) (substs (map Var xs') xs e) (TypeVarType beta)
  let funty = foldr (\ (loc, alpha) ty0 -> FunType (TypeVarType alpha) loc ty0)
                (TypeVarType beta) (zip locs alphas)
  return (funty, gamma',
          Abs (map (\ ((x,_,loc), ty)-> (x,ty,loc))
              (zip xmtyls (map (Just . TypeVarType) alphas)))
                  (substs (map Var xs) xs' e'))

-- ->forall_l=>
typesynthExpr_ gti gamma loc expr@(LocAbs locvars e) = do
  ls' <- replicateM (length locvars) freshLocationVar
  (polylocbodyty, delta, e') <-
    typesynthExpr gti (gamma >++ map CLMarker ls' >++ map CLForall ls')
              loc (locExprSubsts (map LocVar ls') locvars e)
  return (LocAbsType ls' polylocbodyty
         , foldl (\ delta0 l' ->
                     singleoutMarker (CLMarker l')
                       (singleoutMarker (CLForall l') delta0)) delta ls'
         , LocAbs locvars e')

-- ->E
typesynthExpr_ gti gamma loc expr@(App e1 maybeTy e2 maybeLoc) = do
  (a, theta, e1') <- typesynthExpr gti gamma loc e1
  (ty2, loc0, delta, transformFun) <- typeapplysynth gti theta loc (apply theta a) e2
  return (ty2, delta, App (transformFun e1) (Just a) e2 (Just loc0))

-- forall_l E
typesynthExpr_ gti gamma loc expr@(LocApp e maybeTy locs) = do
  (a, theta, e') <- typesynthExpr gti gamma loc e
  (b, delta, transformFun) <- locsapplysynth gti theta loc (apply theta a) locs
  return (b, delta, LocApp (transformFun e) (Just a) locs)

typesynthExpr_ gti gamma loc expr = do
  error $ "typesynth: not implemented yet"


-- | Type application synthesising
--   typeapplysynth Γ loc A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth :: GlobalTypeInfo -> Context -> Location -> Type -> Expr
   -> NameGen (Type, Location, Context, Expr -> Expr)
typeapplysynth gti gamma loc typ e = traceNS "typeapplysynth" (gamma, loc, typ, e) $
  checkwftype gamma typ $
  case typ of
    -- ForallApp
    TypeAbsType alphas a -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- replicateM (length alphas) freshExistsTypeVar
      (typ, loc0, delta, g)
        <- typeapplysynth gti (gamma >++ map CExists alphas') loc
                     (typeSubsts (map TypeVarType alphas') alphas a) e
      return (typ, loc0, delta, g. \f -> TypeApp f (Just typ) (map TypeVarType alphas'))

    -- ForallApp: Not allowed without any explicit location applications
    -- LForall l a -> do
    --   -- Do alpha conversion to avoid clashes
    --   l' <- freshLVar
    --   typeapplysynth (gamma >: CLExists l') loc
    --                  (locSubst (UnknownExists l') l a)
    --                  e

    -- alpha^App
    TypeVarType alpha
     | cExists alpha -> do  -- TExists alpha
      alpha1 <- freshExistsTypeVar
      alpha2 <- freshExistsTypeVar
      l      <- freshExistsLocationVar
      let loc' = LocVar l
      (delta, e') <- typecheckExpr gti (insertAt gamma (CExists alpha) $ context
                            [ CLExists l
                            , CExists alpha2
                            , CExists alpha1
                            , CExistsSolved alpha
                                 $ FunType (TypeVarType alpha1) loc' (TypeVarType alpha2)
                            ])
                         loc
                         e
                         (TypeVarType alpha1)
      return (TypeVarType alpha2, loc', delta, \f -> App f (Just typ) e' (Just loc'))

    -- ->App
    FunType a loc' c -> do
      (delta, e') <- typecheckExpr gti gamma loc e a
      return (c, loc', delta, \f -> App f (Just typ) e' (Just loc'))


    _ -> error $ "typeapplysynth: don't know what to do with: "
              ++ pretty (gamma, loc, typ, e)


-- | Location application synthesising
--   locapplysynth Γ loc A loc0 = (C, Δ) <=> Γ |- A . loc0 =>> C -| Δ
locsapplysynth :: GlobalTypeInfo -> Context -> Location -> Type -> [Location]
  -> NameGen (Type, Context, Expr -> Expr)
locsapplysynth gti gamma loc typ locs0 = traceNS "locsapplysynth" (gamma, loc, typ, locs0) $
  checkwftype gamma typ $
  case typ of
    -- LForall LocApp
    LocAbsType ls a ->  -- Todo: what happens when |locs0| != |ls|?
      return (locSubsts locs0 ls a, gamma, \f -> LocApp f (Just typ) locs0)

    -- TForall LocApp
    TypeAbsType alphas a -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- replicateM (length alphas) freshExistsTypeVar
      (typ', delta, g) <-
        locsapplysynth gti (gamma >++ map CExists alphas') loc
                     (typeSubsts (map TypeVarType alphas') alphas a) locs0
      return (typ', delta, g . \f -> TypeApp f (Just typ) (map TypeVarType alphas'))

    -- alpha^: Not allowed because alpha^ is a monomorphic type variable!

    _ -> error $ "locsapplysynth: don't know what to do with: "
               ++ pretty (gamma, loc, typ, locs0)
