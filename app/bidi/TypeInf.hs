module TypeInf(typeInf) where

import Data.Either
import Data.Maybe
import qualified Data.Set as S

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
  -- elab_bindingDecls <- elaborate gti initEnv partial_elab_bindingDecls

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

elaborate :: Monad m => GlobalTypeInfo -> Env -> [BindingDecl] -> m [BindingDecl]
elaborate gti env [] =  return []
elaborate gti env (bindingDecl@(Binding _ f ty _):bindingDecls) = do
  let gti1 = gti {_bindingTypeInfo = (f,ty):_bindingTypeInfo gti}   -- for self-recursion
  elab_bindingDecl <- elabBindingDecl gti1 env bindingDecl
  elab_bindingDecls <- elaborate gti1 env bindingDecls
  return (elab_bindingDecl:elab_bindingDecls)

elabBindingDecl :: Monad m => GlobalTypeInfo -> Env -> BindingDecl -> m BindingDecl
elabBindingDecl gti env (Binding istop name ty expr) = do -- ToDo: When name is recursive, expr must be lambda abstraction!
  -- let env = emptyEnv{_varEnv=_bindingTypeInfo gti}
  (elab_expr,elab_ty) <- elabExpr gti env clientLoc expr
  if equalType elab_ty ty
  then return (Binding istop name ty elab_expr)
  else error $ "[TypeCheck] elabBindingDecl: Incorrect types: " ++ name ++ "\n" ++ show elab_ty ++ "\n" ++ show ty

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
  elab_letBindingDecls <- elaborate gti1 env partial_elab_letBindingDecls

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
    -- (Client, Client) -> return gamma
    -- (Server, Server) -> return gamma
    (Location c1, Location c2) | c1 == c2 -> return gamma

    (LocVar l1, LocVar l2)
    
    -- <:LVar
    -- (Unknown l1, Unknown l2) | l1 == l2 -> return gamma
    
      | (not (clExists l1)) && (not (clExists l2)) && l1 == l2 -> return gamma
      
    -- <:ExLVar
    -- (UnknownExists l1, UnknownExists l2) | l1 == l2 -> return gamma
    
      | clExists l1 && clExists l2 && l1 == l2 -> return gamma
      
    -- (UnknownExists l, loc) | l `S.notMember` freeLVarsIn loc ->
    --   instantiateLocL gamma l loc

      | otherwise ->
         error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    (LocVar l, loc) 
      | clExists l && l `S.notMember` freeLVarsIn loc ->
          instantiateLocL gamma l loc
        
      | otherwise ->
         error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)
                          
    -- (loc, UnknownExists l) | l `S.notMember` freeLVarsIn loc ->
    --  instantiateLocR gamma loc l

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

{-
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
    Just gamma' -> return gamma'    -- Todo: ??? when a is beta^, which is tau as in InstLReach?
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
      TypeAbsType beta b -> do   -- Should Fix: beta is a list!!
        -- Do alpha conversion to avoid clashes
        beta' <- freshTypeVar
        dropMarker (CForall beta') <$>
          instantiateL (gamma >++ [CForall beta'])
                       alpha
                       (typeSubst (TypeVarType beta') beta b)
      _ -> error $ "The impossible happened! instantiateL: "
                ++ pretty (gamma, alpha, a)

      -- Should Fix: LocAbsType locs b ???
      -- Should Fix: Tuple ???
      -- Should Fix: TypeCon ???

      
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
                              alpha1
                              a1
        instantiateR theta (apply theta a2) alpha2
      -- InstRAIIL
      TypeAbsType beta b -> do   -- Should Fix: beta is a list!!
        -- Do alpha conversion to avoid clashes
        beta' <- freshTypeVar
        dropMarker (CMarker beta') <$>
          instantiateR (gamma >++ [CMarker beta', CExists beta'])
                       (typeSubst (TypeVarType beta') beta b)
                       alpha
      _ -> error $ "The impossible happened! instantiateR: "
                ++ pretty (gamma, a, alpha)

      -- Should Fix: LocAbsType locs b ???
      -- Should Fix: Tuple ???
      -- Should Fix: TypeCon ???

-}
