module TypeInf(typeInf) where

import Data.Either
import Data.Maybe
import qualified Data.Set as S
import Data.Tuple.HT(mapFst, fst3, snd3, thd3)

import Control.Monad (replicateM, foldM)
import Control.Monad.Except
import Control.Monad.State

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

import Debug.Trace

-- Todo
--   1. Apply context to term to replace all occurrences of alpha^ by
--      some type. [Done]
--   2. Apply elabType in type declarations of let bindings [Done]
--   3. Apply elabLocation in the use of locations at expressions and
--      type declarations [Done]
--   4. elabExpr before typeInf [Done]
--   5. Unconstrained existence type variables remain! [Done]
--   6. Type application terms in an argumnet, (...) expr, do not have
--      type annotations. The subtype returns a transformer? [Done]

--   [Remaining questions]
--   7. Should we introduce lambdas over type variables?
--      For example, ... (\x@l. let y: ... a ... = expr) ...
--      How do we know the name of this type variable a when it comes from
--      the inferred type polymorphism as [a]. \x@l. ...?

type TIMonad = ExceptT String (State NameState) -- 'ExceptT String NameGen'

typeInf :: Monad m => Bool -> [TopLevelDecl] -> m (GlobalTypeInfo, [TopLevelDecl], [TopLevelDecl], [TopLevelDecl])
typeInf debug toplevelDecls = do
  -- 1. split
  (bindingDecls, userDatatypes) <- splitTopLevelDecls toplevelDecls

  -- let datatypeDecls = builtinDatatypes ++ userDatatypes
  let datatypeDecls0 = builtinDatatypes
  let datatypeDecls1 = userDatatypes
  let datatypeDecls = datatypeDecls0 ++ datatypeDecls1

  -- 2. collect all types, builtin or user-defined ones
  typeInfo <- collectDataTypeDecls datatypeDecls

  -- 3. elaborate data types
  -- elab_datatypeDecls <- elabDataTypeDecls typeInfo datatypeDecls
  -- elab_datatypeDecls0 <- elabDataTypeDecls typeInfo datatypeDecls0
  -- elab_datatypeDecls1 <- elabDataTypeDecls typeInfo datatypeDecls1
  let elab_datatypeDecls0 = datatypeDecls0
  let elab_datatypeDecls1 = datatypeDecls1
  let elab_datatypeDecls = elab_datatypeDecls0 ++ elab_datatypeDecls1
  dataTypeInfo <- collectDataTypeInfo elab_datatypeDecls

  -- 4. elaborate constructor types
  conTypeInfo <- elabConTypeDecls elab_datatypeDecls

  -- 5. elaborate types declared in the bindings
  -- partial_elab_bindingDecls <- elabBindingTypes typeInfo [] [] bindingDecls
  let partial_elab_bindingDecls = bindingDecls

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

  let libGamma = map (\(x,ty) -> CVar x True ty)
                   (_bindingTypeInfo gti ++ bindingTypeInfo)
  let initGamma = mempty >++ libGamma
  let (elab_bindingDecls) =
        case evalNameGen
               $ runExceptT
                   (do lift $ setDebug debug
                       bidi gti initGamma clientLoc partial_elab_bindingDecls) of
          Left err_msg -> error err_msg -- Uncaught error!!
          Right (_,x) -> x

  -- 7. return elaborated data types and bindings
  let lib_toplevels = [ LibDeclTopLevel x ty | (x,ty) <- basicLibTypeInfo]
  let elab_toplevels0 =
        [ DataTypeTopLevel dt | dt <- elab_datatypeDecls0]
  let elab_toplevels1 =
        [ DataTypeTopLevel dt | dt <- elab_datatypeDecls1]
        ++ [ BindingTopLevel bd | bd <- elab_bindingDecls]

  let gti1 = gti {_bindingTypeInfo=basicLibTypeInfo ++ bindingTypeInfo}

  -- elab_toplevels0 : built-in datatypes
  -- elab_toplevels1 : user-defined datatypes + bindings
  -- lib_toplevels : basic libraries
  return (gti1, elab_toplevels1, elab_toplevels0, lib_toplevels)

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

-- elabDataTypeDecls :: Monad m => TypeInfo -> [DataTypeDecl] -> m [DataTypeDecl]
-- elabDataTypeDecls typeInfo datatypeDecls =
--   mapM (elabDataTypeDecl typeInfo) datatypeDecls

-- elabDataTypeDecl :: Monad m => TypeInfo -> DataTypeDecl -> m DataTypeDecl
-- elabDataTypeDecl typeInfo (DataType name locvars tyvars typeConDecls) = do
--   elab_typeConDecls <- mapM (elabTypeConDecl typeInfo locvars tyvars) typeConDecls
--   return (DataType name locvars tyvars elab_typeConDecls)

-- elabTypeConDecl :: Monad m => TypeInfo -> [String] -> [String] -> TypeConDecl -> m TypeConDecl
-- elabTypeConDecl typeInfo locvars tyvars (TypeCon con tys) = do
--   elab_tys <- mapM (elabType typeInfo tyvars locvars ) tys
--   return (TypeCon con elab_tys)

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

-- elabBindingTypes :: Monad m => TypeInfo -> [String] -> [String] -> [BindingDecl] -> m [BindingDecl]
-- elabBindingTypes typeInfo tyvars locvars bindingDecls =
--   mapM (\(Binding istop f ty expr)-> do
--            -- elab_ty <- elabType typeInfo tyvars locvars ty
--            -- elab_expr <- elabExpr typeInfo tyvars locvars expr
--            -- return (Binding istop f elab_ty elab_expr)) bindingDecls
--            return (Binding istop f ty expr)) bindingDecls

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

bidi :: GlobalTypeInfo -> Context -> Location -> [BindingDecl] -> TIMonad (Context, [BindingDecl])
bidi gti gamma loc bindingDecls =  bidiBindingDecls gti gamma loc bindingDecls

bidiBindingDecls :: GlobalTypeInfo -> Context -> Location -> [BindingDecl] -> TIMonad (Context, [BindingDecl])
bidiBindingDecls gti gamma loc [] =  return (gamma, [])
bidiBindingDecls gti gamma loc (bindingDecl@(Binding _ f ty _):bindingDecls) = do
  let gti1 = gti {_bindingTypeInfo = (f,ty):_bindingTypeInfo gti}   -- for self-recursion
  (gamma1, elab_bindingDecl) <- bidiBindingDecl gti1 gamma loc bindingDecl
  (gamma2, elab_bindingDecls) <- bidiBindingDecls gti1 gamma1 loc bindingDecls
  return (gamma2, elab_bindingDecl:elab_bindingDecls)

bidiBindingDecl :: GlobalTypeInfo -> Context -> Location -> BindingDecl -> TIMonad (Context, BindingDecl)
bidiBindingDecl gti gamma loc (Binding istop name ty expr) = do -- ToDo: When name is recursive, expr must be lambda abstraction!
  (delta, expr') <- typecheckExpr gti gamma clientLoc expr ty
  return (delta, Binding istop name ty expr')  -- apply delta to expr'???

----------------------------------------------------------------------------
-- [Common] Elaboration of types
----------------------------------------------------------------------------
-- elabType :: Monad m => TypeInfo -> [TypeVar] -> [LocationVar] -> Type -> m Type
-- elabType typeInfo tyvars locvars (TypeVarType x) = do
--   if elem x tyvars then return (TypeVarType x)
--   else if isConstructorName x then
--           do (_locvars, _tyvars) <- lookupTypeCon typeInfo x
--              if _locvars ==[] && _tyvars == []
--              then return (ConType x [] [])
--              else error $ "[TypeCheck]: elabType: Invalid type constructor: " ++ x
--        else
--           error $ "[TypeCheck] elabType: Not found: " ++ x ++ " in " ++ show tyvars

-- elabType typeInfo tyvars locvars (TupleType tys) = do
--   elab_tys <- mapM (elabType typeInfo tyvars locvars) tys
--   return (TupleType elab_tys)

-- elabType typeInfo tyvars locvars (FunType ty1 (Location loc) ty2) = do
--   elab_ty1 <- elabType typeInfo tyvars locvars ty1
--   elab_ty2 <- elabType typeInfo tyvars locvars ty2
--   let loc0 = if loc `elem` locvars
--              then LocVar loc else Location loc
--   return (FunType elab_ty1 loc0 elab_ty2)

-- elabType typeInfo tyvars locvars (FunType ty1 loc0@(LocVar _) ty2) = do
--   elab_ty1 <- elabType typeInfo tyvars locvars ty1
--   elab_ty2 <- elabType typeInfo tyvars locvars ty2
--   return (FunType elab_ty1 loc0 elab_ty2)

-- elabType typeInfo tyvars locvars (TypeAbsType abs_tyvars ty) = do
--   elab_ty <- elabType typeInfo (abs_tyvars ++ tyvars) locvars ty
--   return (TypeAbsType abs_tyvars elab_ty)

-- elabType typeInfo tyvars locvars (LocAbsType abs_locvars ty) = do
--   elab_ty <- elabType typeInfo tyvars (abs_locvars ++ locvars) ty
--   return (LocAbsType abs_locvars elab_ty)

-- elabType typeInfo tyvars locvars (ConType name locs tys) = do
--   (_locvars, _tyvars) <- lookupTypeCon typeInfo name
--   if length _locvars == length locs && length _tyvars == length tys
--     then do elab_locs <- mapM (elabLocation locvars) locs
--             elab_tys <- mapM (elabType typeInfo tyvars locvars) tys
--             return (ConType name elab_locs elab_tys)
--     else error $ "[TypeCheck]: elabType: Invalud args for ConType: " ++ name


----------------------------------------------------------------------------
-- [Common] Elaboration of locations
----------------------------------------------------------------------------

-- elabLocation :: Monad m => [LocationVar] -> Location -> m Location
-- elabLocation locvars (Location loc)
--   | loc `elem` locvars = return (LocVar loc)
--   | otherwise = return (Location loc)
-- elabLocation locvars (LocVar x)
--   | x `elem` locvars = return (LocVar x)
--   | otherwise = error $ "[TypeCheck] elabLocation: Not found LocVar " ++ x

----------------------------------------------------------------------------
-- [Common] Elaboration of expressions
----------------------------------------------------------------------------

-- elabExpr :: Monad m => TypeInfo -> [TypeVar] -> [LocationVar] -> Expr -> m Expr
-- elabExpr typeInfo tyvars locvars (Var x) = return $ Var x

-- elabExpr typeInfo tyvars locvars (TypeAbs alphas e) = do
--   e' <- elabExpr typeInfo (alphas++tyvars) locvars e
--   return $ TypeAbs alphas e'

-- elabExpr typeInfo tyvars locvars (LocAbs ls e) = do
--   e' <- elabExpr typeInfo tyvars (ls++locvars) e
--   return $ LocAbs ls e'

-- elabExpr typeInfo tyvars locvars (Abs xMaybetyLocs e) = do
--   xMaybetyLocs' <- mapM ftriple xMaybetyLocs
--   e' <- elabExpr typeInfo tyvars locvars e
--   return $ Abs xMaybetyLocs' e'
--   where
--     ftriple (x,Nothing,loc) = do
--       loc' <- elabLocation locvars loc
--       return (x, Nothing, loc')
--     ftriple (x,Just ty,loc) = do
--       ty' <- elabType typeInfo tyvars locvars ty
--       loc' <- elabLocation locvars loc
--       return (x, Just ty', loc')

-- elabExpr typeInfo tyvars locvars (Let bindingDecls e) = do
--   bindingDecls' <- mapM fBindDecl bindingDecls
--   e' <- elabExpr typeInfo tyvars locvars e
--   return $ Let bindingDecls' e'
--   where
--     fBindDecl (Binding istop x ty expr) = do
--       ty' <- elabType typeInfo tyvars locvars ty
--       expr' <- elabExpr typeInfo tyvars locvars expr
--       return $ Binding istop x ty' expr'

-- elabExpr typeInfo tyvars locvars (Case e maybeTy alts) = do
--   e' <- elabExpr typeInfo tyvars locvars e
--   maybeTy' <- mapM (elabType typeInfo tyvars locvars) maybeTy
--   alts' <- mapM fAlt alts
--   return $ Case e' maybeTy' alts'
--   where
--     fAlt (Alternative c xs expr) = do
--       expr' <- elabExpr typeInfo tyvars locvars expr
--       return $ Alternative c xs expr'
--     fAlt (TupleAlternative xs expr) = do
--       expr' <- elabExpr typeInfo tyvars locvars expr
--       return $ TupleAlternative xs expr'

-- elabExpr typeInfo tyvars locvars (App e1 maybeTy e2 maybeLoc) = do
--   e1' <- elabExpr typeInfo tyvars locvars e1
--   maybeTy' <- fMaybety maybeTy
--   e2' <- elabExpr typeInfo tyvars locvars e2
--   maybeLoc' <- fMaybeloc maybeLoc
--   return $ App e1' maybeTy' e2' maybeLoc'

--   where
--     fMaybety Nothing = return Nothing
--     fMaybety (Just ty) = do
--       ty' <- elabType typeInfo tyvars locvars ty
--       return (Just ty')

--     fMaybeloc Nothing = return Nothing
--     fMaybeloc (Just loc) = do
--       loc' <- elabLocation locvars loc
--       return (Just loc')

-- elabExpr typeInfo tyvars locvars (TypeApp e1 maybeTy tys) = do
--   e1' <- elabExpr typeInfo tyvars locvars e1
--   maybeTy' <- fMaybety maybeTy
--   tys' <- mapM (elabType typeInfo tyvars locvars) tys
--   return $ TypeApp e1' maybeTy' tys'

--   where
--     fMaybety Nothing = return Nothing
--     fMaybety (Just ty) = do
--       ty' <- elabType typeInfo tyvars locvars ty
--       return (Just ty')

-- elabExpr typeInfo tyvars locvars (LocApp e1 maybeTy locs) = do
--   e1' <- elabExpr typeInfo tyvars locvars e1
--   maybeTy' <- fMaybety maybeTy
--   locs' <- mapM (elabLocation locvars) locs
--   return $ LocApp e1' maybeTy' locs'

--   where
--     fMaybety Nothing = return Nothing
--     fMaybety (Just ty) = do
--       ty' <- elabType typeInfo tyvars locvars ty
--       return (Just ty')

-- elabExpr typeInfo tyvars locvars (Tuple exprs) = do
--   exprs' <- mapM (elabExpr typeInfo tyvars locvars) exprs
--   return $ Tuple exprs'

-- elabExpr typeInfo tyvars locvars (Prim op locs tys exprs) = do
--   locs' <- mapM (elabLocation locvars) locs
--   tys' <- mapM (elabType typeInfo tyvars locvars) tys
--   exprs' <- mapM (elabExpr typeInfo tyvars locvars) exprs
--   return $ Prim op locs' tys' exprs'

-- elabExpr typeInfo tyvars locvars (Lit lit) = return $ Lit lit

-- elabExpr typeInfo tyvars locvars (Constr c locs tys exprs argtys) = do
--   locs' <- mapM (elabLocation locvars) locs
--   tys' <- mapM (elabType typeInfo tyvars locvars) tys
--   exprs' <- mapM (elabExpr typeInfo tyvars locvars) exprs
--   argtys' <- mapM (elabType typeInfo tyvars locvars) argtys
--   return $ Constr c locs' tys' exprs' argtys'

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

----------------------------------------------------------------------------
-- Common Utils
----------------------------------------------------------------------------
allUnique [] = []
allUnique (x:xs) =
  if elem x xs then [x] else allUnique xs

----------------------------------------------------------------------------
-- For bidirectional typechecking
----------------------------------------------------------------------------

nolib (Context gamma) = Context $ reverse (drop 0 (reverse gamma))

-- | Algorithmic sublocation:
subloc :: Context -> Location -> Location -> TIMonad Context
subloc gamma loc1 loc2 =
  traceNS "subloc" (nolib gamma, loc1, loc2) $
  checkwfloc gamma loc1 $ checkwfloc gamma loc2 $
    case (loc1, loc2) of
    -- <:Loc
    (Location c1, Location c2) | c1 == c2 -> return gamma

    (LocVar l1, LocVar l2)
      | (not (clExists l1)) && (not (clExists l2)) && l1 == l2 -> return gamma
      | clExists l1 && clExists l2 && l1 == l2 -> return gamma
      | clExists l1
          && l1 `elem` lexistentials gamma
          && l1 `S.notMember` freeLVarsIn (LocVar l2) -> do
            instantiateLocL gamma l1 (LocVar l2)
      | clExists l2
          && l2 `elem` lexistentials gamma
          && l2 `S.notMember` freeLVarsIn (LocVar l1) -> do
            instantiateLocR gamma (LocVar l1) l2
      | otherwise ->
         throwError $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    (LocVar l, loc)
      | clExists l && l `S.notMember` freeLVarsIn loc ->
          instantiateLocL gamma l loc
      | otherwise ->
         throwError $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    (loc, LocVar l)
      | clExists l && l `S.notMember` freeLVarsIn loc ->
          instantiateLocR gamma loc l
      | otherwise ->
         throwError $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

    _ -> throwError $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)


-- | Algorithmic instantiation location (left):
--   instantiateLocL Γ l loc = Δ <=> Γ |- l^ :=< loc -| Δ
instantiateLocL gamma l loc
  | clExists l =
    traceNS "instantiateLocL" (nolib gamma, l, loc) $
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
            throwError $ "instantiateLocL: not ended with ^: " ++ l'
      _ -> throwError $ "The impossible happened! instantiateLocL: "
                ++ pretty (gamma, LocVar l, loc)

  | otherwise =
    throwError $ "instantiateLocL: not ended with ^: " ++ l


-- | Algorithmic instantiation location (right):
--   instantiateLocR Γ loc l = Δ <=> Γ |- loc =:< l -| Δ
instantiateLocR gamma loc l
  | clExists l =
    traceNS "instantiateLocR" (nolib gamma, loc, l) $
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
              throwError $ "instantiateLocR: not ended with ^: " ++ l'

        _ -> throwError $ "The impossible happened! instantiateLocR: "
                  ++ pretty (gamma, loc, LocVar l)

  | otherwise =
    throwError $ "instantiateLocR: not ended with ^: " ++ l

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Context -> Location -> Type -> Type -> TIMonad (Context, Expr -> Expr)
subtype gamma loc0 typ1 typ2 =
  traceNS "subtype" (nolib gamma, loc0, typ1, typ2) $
  checkwftype gamma typ1 $ checkwfloc gamma loc0 $ checkwftype gamma typ2 $
    case (typ1, typ2) of
    -- <:Var
    (TypeVarType alpha, TypeVarType alpha')
      | not (cExists alpha) && not (cExists alpha')
          && alpha == alpha' -> return (gamma, \x->x)
      | cExists alpha && cExists alpha'
          && alpha == alpha' && alpha `elem` existentials gamma -> do
          return (gamma, \x->x)
      | cExists alpha
          && alpha `elem` existentials gamma
          && alpha `S.notMember` freeTVars (TypeVarType alpha') -> do
          delta <- instantiateL gamma alpha (TypeVarType alpha')
          return (delta, \x->x)
      | cExists alpha'
          && alpha' `elem` existentials gamma
          && alpha' `S.notMember` freeTVars (TypeVarType alpha) -> do
          delta <- instantiateR gamma (TypeVarType alpha) alpha'
          return (delta, \x->x)
      | otherwise ->
          throwError $ "subtype(TypeVarType,TypeVarType), don't know what to do with: "
                         ++ pretty (gamma, typ1, typ2)

    (TypeVarType alpha, a)
      | cExists alpha
          && alpha `elem` existentials gamma
          && alpha `S.notMember` freeTVars a -> do
          delta <- instantiateL gamma alpha a
          return (delta, \x->x)

    (a, TypeVarType alpha)
      | cExists alpha
          && alpha `elem` existentials gamma
          && alpha `S.notMember` freeTVars a -> do
          delta <- instantiateR gamma a alpha
          return (delta, \x->x)

    -- <:TupleType
    (TupleType tys1, TupleType tys2)
      | length tys1 == length tys2 -> do
         (delta, fs) <-
           foldM (\ (g,fs) (maybety1,maybety2) ->
                  case (maybety1, maybety2) of
                    (Just ty1, Just ty2) -> do
                        (g', f) <- subtype g loc0 ty1 ty2
                        return (g', fs++[f])
                    _ -> throwError $ "subtype: TupleType: not monotype: "
                                    ++ pretty (gamma, typ1, typ2))
           (gamma,[]) (zip (map monotype tys1) (map monotype tys2))
         xs <- lift $ replicateM (length tys1) freshVar
         return (delta,
                 \x -> Case x (Just (TupleType (map (apply delta) tys2)))
                         [TupleAlternative xs
                            (Tuple [f (Var x) | (f,x) <- zip fs xs])])

    -- <:->
    (FunType a1 loc1 a2, FunType b1 loc2 b2) -> do
      (theta, f) <- subtype gamma loc0 b1 a1
      (delta, g) <- subtype theta loc0 (apply theta a2) (apply theta b2)
      delta' <- subloc delta (lapply delta loc1) (lapply delta loc2)
      x <- lift $ freshVar
      return (delta',
        \h -> Abs [(x, Just (apply delta' b1), lapply delta' loc2)]
                (g (App h (Just $ apply delta' (FunType a1 loc1 a2))
                      (f (Var x)) (Just loc0) )))

    -- <:forallR
    (a, TypeAbsType alphas b) -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- lift $ replicateM (length alphas) freshTypeVar
      (theta, f) <- subtype (gamma >++ map CForall alphas') loc0 a
                      (typeSubsts (map TypeVarType alphas') alphas b)
      let delta = dropMarker (CForall (head alphas')) theta
      return (delta, \x -> TypeAbs alphas (f x))

    -- <:forallL
    (TypeAbsType alphas a, b) -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- lift $ replicateM (length alphas) freshExistsTypeVar
      (theta, f) <- subtype (gamma >++ map CMarker alphas' >++ map CExists alphas') loc0
                      (typeSubsts (map TypeVarType alphas') alphas a) b
      let delta = dropMarker (CMarker (head alphas')) theta
      let tys = map (apply theta) (map TypeVarType alphas')
      return (delta, \x -> f (TypeApp x (Just $ apply delta (TypeAbsType alphas a)) tys))

    -- forallLoc
    (LocAbsType locvars1 a, LocAbsType locvars2 b)
      | locvars1 == locvars2 -> subtype gamma loc0 a b
      | length locvars1 == length locvars2 -> do
         locvars <- lift $ replicateM (length locvars1) freshLocationVar
         (theta, f) <- subtype (gamma >++ map CLMarker locvars) loc0
                         (locSubsts (map LocVar locvars) locvars1 a)
                         (locSubsts (map LocVar locvars) locvars2 a)
         let delta = dropMarker (CLMarker (head locvars)) theta
         return (delta, f)
      | otherwise ->
         throwError $ "subtype: different length of location vars: "
                           ++ pretty (gamma, typ1, typ2)

    -- <:ConType
    (ConType c1 locs1 tys1, ConType c2 locs2 tys2)
      | c1 /= c2 || length locs1 /= length locs2 || length tys1 /= length tys2 ->
          throwError $ "subtype: ConType: different type constructors: "
                  ++ pretty (gamma, typ1, typ2)
      | otherwise -> do
          delta <- foldM (\ g (loc1, loc2) -> subloc g loc1 loc2) gamma (zip locs1 locs2)
          delta' <- foldM (\ g (maybety1, maybety2) ->
                      case (maybety1, maybety2) of
                        (Just ty1, Just ty2) -> do
                             (g', _) <- subtype g loc0 ty1 ty2  -- TODO: transform functions for sum types !!
                             return g'
                        _ -> throwError $ "subtype: ConType: not monotype: "
                                     ++ pretty (gamma, typ1, typ2))
                    delta (zip (map monotype tys1) (map monotype tys2))
          return (delta', \x->x) -- TODO: transform functions for sum types !!

    _ -> throwError $ "subtype, don't know what to do with: "
                           ++ pretty (gamma, typ1, typ2)


-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Context -> TypeVar -> Type -> TIMonad Context
instantiateL gamma alpha a = 
  traceNS "instantiateL" (nolib gamma, TypeVarType alpha, a) $
  instantiateL' gamma alpha a

instantiateL' gamma alpha a
  | cExists alpha = instantiateL_ gamma alpha a
  | otherwise = throwError $ "instantiateL: not ended with ^: " ++ alpha

instantiateL_ gamma alpha a =
  checkwftype gamma a $ checkwftype gamma (TypeVarType alpha) $
  case solve gamma alpha =<< monotype a of
    -- InstLSolve :
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstLReach
      TypeVarType beta
        | not (cExists beta) ->
            throwError $ "instantiateL: InstLReach: not ended with ^: " ++ beta
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TypeVarType alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TypeVarType beta)

      -- InstLArr
      FunType a1 loc a2   -> do
        alpha1 <- lift $ freshExistsTypeVar
        alpha2 <- lift $ freshExistsTypeVar
        l      <- lift $ freshExistsLocationVar
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
        betas' <- lift $ replicateM (length betas) freshTypeVar
        dropMarker (CForall (head betas')) <$> -- Todo: Ensure that betas is not null!
          instantiateL (gamma >++ map CForall betas')
                       alpha
                       (typeSubsts (map TypeVarType betas') betas b)

      -- Note: No polymorphic (location) abstraction is allowed.

      -- InstLAIIL
      -- LocAbsType locs b -> do  -- Should not be allowed!!

      -- Note: TupleType and ConType should be monomorphic types that
      --       will be handled above.

      -- InstLConstr
      ConType c locs tys -> do
        ls <- lift $ replicateM (length locs) freshExistsLocationVar
        betas <- lift $ replicateM (length tys) freshExistsTypeVar
        let gammaReplace = context
               $ map CLExists ls ++ map CExists betas ++ 
                 [CExistsSolved alpha
                    (ConType c (map LocVar ls) (map TypeVarType betas))]
        let gamma0 = insertAt gamma (CExists alpha) gammaReplace
        
        gamma1 <- foldM (\gamma (l, loc) -> instantiateLocL gamma l loc)
                    gamma0 (zip ls locs)
               
        foldM (\gamma (beta, argty) -> instantiateL gamma beta argty)
                 gamma1 (zip betas tys)

      -- InstLTupleType
      TupleType argTys -> do
        betas <- lift $ replicateM (length argTys) freshExistsTypeVar
        let gammaReplace = context
               $ map CExists betas ++
                 [CExistsSolved alpha (TupleType (map TypeVarType betas))]
        let gamma0 = insertAt gamma (CExists alpha) gammaReplace
        
        foldM (\gamma (beta, argty) -> instantiateL gamma beta argty)
                 gamma0 (zip betas argTys)
        
      _ -> throwError $ "The impossible happened! instantiateL: "
                ++ pretty (gamma, TypeVarType alpha, a)


-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Context -> Type -> TypeVar -> TIMonad Context
instantiateR gamma a alpha =
  traceNS "instantiateR" (nolib gamma, a, TypeVarType alpha) $
  instantiateR' gamma a alpha
  
instantiateR' gamma a alpha
  | cExists alpha = instantiateR_ gamma a alpha
  | otherwise = throwError $ "instantiateR: not ended with ^: " ++ alpha

instantiateR_ gamma a alpha =
  checkwftype gamma a $ checkwftype gamma (TypeVarType alpha) $
  case solve gamma alpha =<< monotype a of
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstRReach
      TypeVarType beta
        | not (cExists beta) ->
            throwError $ "instantiateR: InstRReach: not ended with ^: " ++ beta
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TypeVarType alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TypeVarType beta)

      -- InstRArr
      FunType a1 loc a2   -> do
        alpha1 <- lift $ freshExistsTypeVar
        alpha2 <- lift $ freshExistsTypeVar
        l      <- lift $ freshExistsLocationVar
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
        betas' <- lift $ replicateM (length betas) freshTypeVar
        dropMarker (CMarker (head betas')) <$>
          instantiateR (gamma >++ map CMarker betas' >++ map CExists betas')
                       (typeSubsts (map TypeVarType betas') betas b)
                       alpha

      -- Note: No polymorphic (location) abstraction is allowed.

      -- InstLAIIR
      -- LocAbsType locs b -> do  -- Should not be allowed!!

      -- Note: TupleType and ConType should be monomorphic types that
      --       will be handled above.

      -- InstRConstr
      ConType c locs tys -> do
        ls <- lift $ replicateM (length locs) freshExistsLocationVar
        betas <- lift $ replicateM (length tys) freshExistsTypeVar
        let gammaReplace = context
               $ map CLExists ls ++ map CExists betas ++ 
                 [CExistsSolved alpha
                    (ConType c (map LocVar ls) (map TypeVarType betas))]
        let gamma0 = insertAt gamma (CExists alpha) gammaReplace
        
        gamma1 <- foldM (\gamma (l, loc) -> instantiateLocR gamma loc l)
                    gamma0 (zip ls locs)
               
        foldM (\gamma (beta, argty) -> instantiateR gamma argty beta)
                 gamma1 (zip betas tys)

      -- InstRTuple
      TupleType argTys -> do
        betas <- lift $ replicateM (length argTys) freshExistsTypeVar
        let gammaReplace = context
               $ map CExists betas ++
                 [CExistsSolved alpha (TupleType (map TypeVarType betas))]
        let gamma0 = insertAt gamma (CExists alpha) gammaReplace

        foldM (\gamma (argty, beta) -> instantiateR gamma argty beta)
                 gamma0 (zip argTys betas)
        
      _ -> throwError $ "The impossible happened! instantiateR: "
                ++ pretty (gamma, a, TypeVarType alpha)


-- | Type checking:
--   typecheck Γ loc e A = Δ <=> Γ |-_loc e <= A -| Δ
typecheckExpr :: GlobalTypeInfo -> Context -> Location -> Expr -> Type -> TIMonad (Context, Expr)
typecheckExpr gti gamma loc expr typ =
  traceNS "typecheck" (nolib gamma, loc, expr, typ) $ checkwftype gamma typ $
  typecheckExpr_ gti gamma loc expr typ

typecheckExpr_ :: GlobalTypeInfo -> Context -> Location -> Expr -> Type -> TIMonad (Context, Expr)

-- ForallI
typecheckExpr_ gti gamma loc e (TypeAbsType alphas a) = do
  -- Do alpha conversion to avoid clashes
  alphas' <- lift $ replicateM (length alphas) freshTypeVar
  (gamma', e') <-
       typecheckExpr gti (gamma >++ map CForall alphas')
          loc
          (tyExprSubsts (map TypeVarType alphas') alphas e)
          (typeSubsts (map TypeVarType alphas') alphas a)
  let instgamma' = instUnsolved (CForall (head alphas')) gamma'
  let delta = dropMarker (CForall (head alphas')) gamma'
  return (delta,
          TypeAbs alphas
            (tyExprSubsts (map TypeVarType alphas) alphas' (eapply instgamma' e')))

-- LForallI
typecheckExpr_ gti gamma loc (LocAbs ls0 e) (LocAbsType ls1 a) = do
  ls' <- lift $ replicateM (length ls0) freshLocationVar
  (gamma', e') <-
    typecheckExpr gti (gamma >++ map CLForall ls') loc
      (locExprSubsts (map LocVar ls') ls0 e) (locSubsts (map LocVar ls') ls1 a)
  let instgamma' = instUnsolved (CLForall (head ls')) gamma'
  let delta = dropMarker (CLForall (head ls')) gamma'
  return (delta, LocAbs ls0 (locExprSubsts (map LocVar ls0) ls' (eapply instgamma' e')))

-- ->I
typecheckExpr_ gti gamma loc (Abs [] e) a = do
  typecheckExpr_ gti gamma loc e a

typecheckExpr_ gti gamma loc (Abs [(x,mty,loc0)] e) (FunType a loc' b) = do
  -- loc0' <- elabLocation (locVars gamma) loc0
  let loc0' = loc0
  x' <- lift $ freshVar
  gamma0 <- subloc gamma loc' loc0'
  (gamma1, e') <- typecheckExpr_ gti (gamma0 >++ [cvar x' a]) loc0' (subst (Var x') x e) b
  let instgamma1 = instUnsolved (cvar x' a) gamma1
  let delta = dropMarker (cvar x' a) gamma1
  return (delta, Abs [(x,Just (apply delta a), loc0')] (subst (Var x) x' (eapply instgamma1 e')))

typecheckExpr_ gti gamma loc (Abs ((x,mty,loc0):xmtyls) e) (FunType a loc' b) = do
  -- loc0' <- elabLocation (locVars gamma) loc0
  let loc0' = loc0
  x' <- lift $ freshVar
  gamma0 <- subloc gamma loc' loc0'
  (gamma1, e') <- typecheckExpr_ gti (gamma0 >++ [cvar x' a]) loc0' (subst (Var x') x (Abs xmtyls e)) b
  let instgamma1 = instUnsolved (cvar x' a) gamma1
  let delta = dropMarker (cvar x' a) gamma1

  return (delta, Abs [(x,Just (apply delta a),loc0')] (subst (Var x) x' (eapply instgamma1 e')))

-- Case
typecheckExpr_ gti gamma loc (Case expr _ alts) caseExprTy = do
  (ty1, gamma0, alts') <- typecheckAlts gti gamma loc alts caseExprTy
  (gamma', expr') <- typecheckExpr gti gamma0 loc expr ty1
  return (gamma', eapply gamma' (Case expr' (Just ty1) alts'))


-- Sub
typecheckExpr_ gti gamma loc e b = do
  (a, theta, e') <- typesynthExpr gti gamma loc e
  (delta, transform) <- subtype theta loc (apply theta a) (apply theta b)
  return (delta, transform e')

-- typecheckExpr_ gti gamma loc e typ = do
--   throwError $ "typecheckExpr: not implemented yet"

-- | Alternative synthesising:
--   typesynthAlt Γ loc alts = (D B, A, Δ) <=> Γ |- alt => D B, A -| Δ
typecheckAlts :: GlobalTypeInfo -> Context -> Location -> [Alternative] -> Type -> TIMonad (Type, Context, [Alternative])
typecheckAlts gti gamma loc alts altsRetTy =
  traceNS "typecheckAlts" (nolib gamma, loc, alts, altsRetTy) $ checkwf gamma $
  if valid alts then typecheckAlts_ gti gamma loc alts altsRetTy
  else throwError $ "[TypeInf] typecheckAlts: invalid alternatives"

  where
    valid alts = oneTupleAlt alts || conAlts alts

    oneTupleAlt [TupleAlternative _ _] = True
    oneTupleAlt _ = False

    conAlts [] = False   -- Having an empty alternative is error!!
    conAlts [Alternative _ _ _] = True
    conAlts ((Alternative _ _ _):alts) = conAlts alts

typecheckAlts_ :: GlobalTypeInfo -> Context -> Location -> [Alternative] -> Type -> TIMonad (Type, Context, [Alternative])
typecheckAlts_ gti gamma loc (alt:alts) altsRetTy = do  -- Always more than zero!
  alpha <- lift $ freshTypeVar
  (ty,gamma',alt') <- typecheckAlt gti gamma loc alt altsRetTy
  foldM (\ (ty0,gamma0,alts0) alt0 -> do
           (ty1,gamma1,alt1) <- typecheckAlt gti gamma0 loc alt0 altsRetTy
           (gamma2, _) <- subtype gamma1 loc (apply gamma1 ty0)  (apply gamma1 ty1)
           return (apply gamma2 ty1, gamma2, alts0++[alt1])
        ) (ty,gamma',[alt']) alts

typecheckAlt gti gamma loc alt altsRetTy =
  traceNS "typecheckAlt" (nolib gamma, loc, alt) $ checkwf gamma $
  typecheckAlt_ gti gamma loc alt altsRetTy

-- Tuple alternative
typecheckAlt_ gti gamma loc (TupleAlternative args expr) altsRetTy = do
  alphas <- lift $ replicateM (length args) freshExistsTypeVar
  -- beta   <- lift $ freshExistsTypeVar
  xs     <- lift $ replicateM (length args) freshVar
  let expr0 = substs (map Var xs) args expr
  (delta, expr')
     <- typecheckExpr gti
          (gamma >++ map CExists alphas
                 -- >++ [CExists beta]
                 >++ [ cvar x (TypeVarType alpha) | (x, alpha) <- zip xs alphas ])
          loc expr0 altsRetTy 
  let expr0' = substs (map Var args) xs expr'          
  return (TupleType (map (apply delta) (map TypeVarType alphas))
         , delta, TupleAlternative args expr0')

-- Data constructor alternative
typecheckAlt_ gti gamma loc (Alternative con args expr) altsRetTy = do
  case lookupConFromDataTypeInfo gti con loc of
    ((locvars,tyvars,argtys,datatypename):_) ->
      if length argtys==length args
      then do
        ls <- lift $ replicateM (length locvars) freshExistsLocationVar
        alphas <- lift $ replicateM (length tyvars) freshExistsTypeVar
        xs <- lift $ replicateM (length args) freshVar

        let substLoc = zip locvars (map LocVar ls)
        let substTy = zip tyvars (map TypeVarType alphas)

        let substedArgtys = map (doSubst substTy . doSubstLoc substLoc) argtys

        let expr0 = substs (map Var xs) args expr
        
        (gamma', expr') <-
          typecheckExpr gti
            (gamma >++ map CLExists ls >++ map CExists alphas 
                   >++ map (uncurry cvar) (zip xs substedArgtys))
               loc expr0 altsRetTy

        let expr0' = substs (map Var args) xs expr'

        return (ConType datatypename
                  (map (lapply gamma') (map LocVar ls))
                  (map (apply gamma') (map TypeVarType alphas))
               , gamma', Alternative con args expr0')

      else throwError $ "[TypeInf] typecheckAlt: invalid arg length: " ++ con ++ show args

    [] -> throwError $ "[TypeInf] typecheckAlt: constructor not found" ++ con



-- | Type synthesising:
--   typesynth Γ loc e = (A, Δ) <=> Γ |- e => A -| Δ
typesynthExpr :: GlobalTypeInfo -> Context -> Location -> Expr -> TIMonad (Type, Context, Expr)
typesynthExpr gti gamma loc expr =
  traceNS "typesynthExpr" (nolib gamma, loc, expr) $ checkwf gamma $
  typesynthExpr_ gti gamma loc expr

-- Var
typesynthExpr_ gti gamma loc expr@(Var x)
  | isConstructorName x =
      case lookupConstr gti x  of
        ((argtys, tyname, locvars, tyvars):_)
           -> do let (e', ty') = mkLocAbs loc x tyname locvars tyvars argtys
                 return (ty', gamma, e')

        [] -> throwError $ "[TypeInf] typesynthExpr: Not found constructor " ++ x

  | otherwise =
      case findVarType gamma x of
        Just x_ty -> return ( x_ty, gamma, expr )
        Nothing -> (throwError $ "typesynth: not in scope " ++ pretty (expr, gamma))

-- Anno
-- typesynthExpr_ gti gamma loc expr@(EAnno e a) = do
--   (delta, e') <- typecheck gamma loc e a
--   return (a, delta, e')

-- ->I=> Original rule
typesynthExpr_ gti gamma loc expr@(Abs xmtyls e) = do
  xs'    <- lift $ replicateM (length xmtyls) freshVar
  alphas <- lift $ replicateM (length xmtyls) freshExistsTypeVar
  beta   <- lift $ freshExistsTypeVar
  -- locs <- mapM (elabLocation (locVars gamma)) $ map thd3 xmtyls
  let locs = map thd3 xmtyls
  let xs = map fst3 xmtyls
  let funty = foldr (\ (loc0, alpha0) ty0 -> FunType (TypeVarType alpha0) loc0 ty0)
                (TypeVarType beta) (zip locs alphas)
  (gamma', e') <- typecheckExpr gti
                    (gamma >++ map CExists alphas
                           >++ [CExists beta]
                           >++ map (uncurry cvar)
                                   (zip xs' (map TypeVarType alphas)))
                      (last locs) (substs (map Var xs') xs e) (TypeVarType beta)
  let instgamma' = instUnsolved (cvar (last xs') (TypeVarType (last alphas))) gamma'
  let delta = dropMarker (cvar (head xs') (TypeVarType (head alphas))) gamma'  -- Todo: Confirm head not last.
  return (apply delta funty, delta,
          singleAbs $
          Abs (map (\ ((x,_,loc), ty)-> (x,ty,loc))
              (zip xmtyls (map (Just . apply delta . TypeVarType) alphas)))
                  (substs (map Var xs) xs' (eapply instgamma' e')))

-- ->forall_l=>
typesynthExpr_ gti gamma loc expr@(LocAbs locvars e) = do
  ls' <- lift $ replicateM (length locvars) freshLocationVar
  (polylocbodyty, delta, e') <-
    typesynthExpr gti (gamma >++ map CLMarker ls' >++ map CLForall ls')
              loc (locExprSubsts (map LocVar ls') locvars e)
  return (LocAbsType locvars (locSubsts (map LocVar locvars) ls' polylocbodyty)
         , foldl (\ delta0 l' ->
                     singleoutMarker (CLMarker l')
                       (singleoutMarker (CLForall l') delta0)) delta ls'
         , singleLocAbs $
           LocAbs locvars (locExprSubsts (map LocVar locvars) ls' e'))

-- Let
typesynthExpr_ gti gamma loc (Let letBindingDecls expr) = do
  let typeInfo = _typeInfo gti
  -- partial_elab_letBindingDecls
  --   <- elabBindingTypes typeInfo (typeVars gamma) (locVars gamma) letBindingDecls
  let partial_elab_letBindingDecls = letBindingDecls
        
  letBindingTypeInfo <- bindingTypes partial_elab_letBindingDecls -- for let body

  (gammaExt, letBindingDecls', subst') <-
    foldM
      (\ (gamma0, binds0, subst0) (Binding istop name ty0 expr0) -> do
          name' <- lift $ freshVar
          let gamma1 = gamma0 >++ [cvar name' ty0]
          let subst1 = subst0 ++ [(Var name', name)]
          (gamma1', expr0') <-
            typecheckExpr gti gamma1 loc (substs_ subst1 expr0) ty0
          let revsubst1 = [(Var x, x') | (Var x', x) <- subst1]
          let binds1 = binds0 ++ [Binding istop name ty0 (substs_ revsubst1 expr0')]
          return (gamma1', binds1, subst1))
      (gamma, [], []) partial_elab_letBindingDecls

  (letty, delta, expr') <- typesynthExpr gti gammaExt loc (substs_ subst' expr)

  let (headx, headty) = head letBindingTypeInfo
  let headx' = head [ x' | (Var x', x) <- subst', headx == x ]
  let delta' = dropMarker (cvar headx' headty) delta
  let revsubst' = [(Var x, x') | (Var x', x) <- subst']
        
  return (apply delta letty, delta', Let letBindingDecls' (substs_ revsubst' expr')) -- Todo: confirm letty vs. apply delta letty

-- Case
-- typesynthExpr_ gti gamma loc (Case expr _ alts) = do
--   (ty1, ty2, gamma0, alts') <- typesynthAlts gti gamma loc alts
--   (gamma', expr') <- typecheckExpr gti gamma0 loc expr ty1
--   return (apply gamma' ty2, gamma', eapply gamma' (Case expr' (Just ty1) alts'))

-- ->E
typesynthExpr_ gti gamma loc expr@(App e1 maybeTy e2 maybeLoc) = do
  (a, theta, e1') <- typesynthExpr gti gamma loc e1
  (ty2, loc0, delta, transformFun) <- typeapplysynth gti theta loc (apply theta a) e2
  return (ty2, delta, transformFun e1') -- App (transformFun e1') (Just . apply delta $ a) e2 (Just loc0)

-- forall_l E
typesynthExpr_ gti gamma loc expr@(LocApp e maybeTy locs0) = do
  -- locs <- mapM (elabLocation (locVars gamma)) locs0
  let locs = locs0
  (a, theta, e') <- typesynthExpr gti gamma loc e
  (b, delta, transformFun) <- locsapplysynth gti theta loc (apply theta a) locs
  return (b, delta, transformFun e') -- LocApp (transformFun e') (Just . apply delta $ a) locs

-- Tuple
typesynthExpr_ gti gamma loc expr@(Tuple es) = do
  (gamma', tys', es') <-
    foldM (\ (gamma0, tys0, es0) e0 -> do
            (ty1, gamma1, e1) <- typesynthExpr gti gamma0 loc e0
            return (gamma1, tys0++[ty1], es0++[e1])
          ) (gamma, [], []) es
  return (TupleType tys', gamma', Tuple es')

-- Prim
{- Note that we safely assume that op_tys is explicitly given.

   Two groups of primitives:
    (1) +, -, *, /, <, <=, >, >=, !=, read, print, intoToString, concat  (cf. not???)
    (2) !, :=, ref

   In (1), no type argumnet is required.

   In (2), the surface language does not use PrimRefCreateOp, but it uses !
   (!) is a wrapper of PrimRefCreateOp, and it explicitly provides type arguments.
-}
typesynthExpr_ gti gamma loc expr@(Prim op op_locs@[] op_tys@[] exprs) =
  typesynthExpr_ gti gamma loc (Prim op [loc] op_tys exprs)

typesynthExpr_ gti gamma loc expr@(Prim op op_locs0 op_tys0 exprs) = do
  let op_locs = op_locs0
  let op_tys  = op_tys0
  -- op_locs <- mapM (elabLocation (locVars gamma)) op_locs0
  -- op_tys  <- mapM (elabType (_typeInfo gti) (typeVars gamma) (locVars gamma)) op_tys0
  case op of
    EqPrimOp -> overloadedEq op_locs op_tys exprs -- EqPrimOp by Parser!!
    NeqPrimOp -> overloadedNeq op_locs op_tys exprs -- NeqPrimOp by Parser!!
    _ -> nonoverloaded op_locs op_tys exprs op

  where
    overloadedEq locs tys exprs =
      (catchError (nonoverloaded locs tys exprs EqIntPrimOp) (\err ->
         (catchError (nonoverloaded locs tys exprs EqBoolPrimOp) (\err ->
            (catchError (nonoverloaded locs tys exprs EqStringPrimOp) (\err ->
               throwError $ "[TypeInf] typesynthExpr: No overloaded match (==):" ++ show op))))))

    overloadedNeq locs tys exprs =
      (catchError (nonoverloaded locs tys exprs NeqIntPrimOp) (\err ->
         (catchError (nonoverloaded locs tys exprs NeqBoolPrimOp) (\err ->
            (catchError (nonoverloaded locs tys exprs NeqStringPrimOp) (\err ->
               throwError $ "[TypeInf] typesynthExpr: No overloaded match (!=):" ++ show op))))))

    nonoverloaded locs tys exprs op =
      case lookupPrimOpType op of
        ((locvars, tyvars, argtys, retty):_) ->
          if length locvars==length locs
             && length tyvars==length tys
             && length argtys==length exprs
          then do
            let substLoc = zip locvars locs
            let substTy  = zip tyvars tys
            let substed_argtys = map (doSubstLoc substLoc . doSubst substTy) argtys
            let substed_retty = doSubstLoc substLoc . doSubst substTy $ retty
            (gamma0, exprs0) <-
               foldM (\ (gamma',exprs') (ty',expr') -> do
                 (gamma'', expr'') <- typecheckExpr gti gamma' loc expr' (apply gamma' ty')
                 return (gamma'', exprs'++[expr'']) )
                    (gamma,[]) (zip substed_argtys exprs)
            return (apply gamma0 substed_retty, gamma0, Prim op locs tys exprs0)


          else throwError $ "[TypeInf] typesynthExpr: incorrect arg locations/types in Prim: " ++ show op

        [] -> throwError $ "[TypeInf] typesynthExpr: type not found in Prim op: " ++ show op



-- Lit
typesynthExpr_ gti gamma loc expr@(Lit literal) =
  return (typeOfLiteral literal, gamma, Lit literal)

-- Constr: No constructor is exposed to programmers.

typesynthExpr_ gti gamma loc expr = do
  throwError $ "typesynth: not implemented yet"


-- | Alternative synthesising:
--   typesynthAlt Γ loc alts = (D B, A, Δ) <=> Γ |- alt => D B, A -| Δ
-- typesynthAlts :: GlobalTypeInfo -> Context -> Location -> [Alternative] -> TIMonad (Type, Type, Context, [Alternative])
-- typesynthAlts gti gamma loc alts =
--   traceNS "typesynthAlts" (nolib gamma, loc, alts) $ checkwf gamma $
--   if valid alts then typesynthAlts_ gti gamma loc alts
--   else throwError $ "[TypeInf] typesynthAlts: invalid alternatives"

--   where
--     valid alts = oneTupleAlt alts || conAlts alts

--     oneTupleAlt [TupleAlternative _ _] = True
--     oneTupleAlt _ = False

--     conAlts [] = False   -- Having an empty alternative is error!!
--     conAlts [Alternative _ _ _] = True
--     conAlts ((Alternative _ _ _):alts) = conAlts alts

-- typesynthAlts_ :: GlobalTypeInfo -> Context -> Location -> [Alternative] -> TIMonad (Type, Type, Context, [Alternative])
-- typesynthAlts_ gti gamma loc (alt:alts) = do  -- Always more than zero!
--   alpha <- lift $ freshTypeVar
--   (ty,ty',gamma',alt') <- typesynthAlt gti gamma loc alt
--   foldM (\ (ty0,ty0',gamma0,alts0) alt0 -> do
--            (ty1,ty1',gamma1,alt1) <- typesynthAlt gti gamma0 loc alt0
--            (gamma2, _) <- subtype gamma1 loc (apply gamma1 ty0)  (apply gamma1 ty1)
--            (gamma3, _) <- subtype gamma2 loc (apply gamma2 ty0') (apply gamma2 ty1')
--            return (apply gamma3 ty1, apply gamma3 ty1', gamma3, alts0++[alt1])
--         ) (ty,ty',gamma',[alt']) alts

-- typesynthAlt gti gamma loc alt =
--   traceNS "typesynthAlt" (nolib gamma, loc, alt) $ checkwf gamma $
--   typesynthAlt_ gti gamma loc alt

-- Tuple alternative
-- typesynthAlt_ gti gamma loc (TupleAlternative args expr) = do
--   alphas <- lift $ replicateM (length args) freshExistsTypeVar
--   -- beta   <- lift $ freshExistsTypeVar
--   xs     <- lift $ replicateM (length args) freshVar
--   let expr0 = substs (map Var xs) args expr
--   (exprTy, delta, expr')
--      <- typesynthExpr gti
--           (gamma >++ map CExists alphas
--                  -- >++ [CExists beta]
--                  >++ [ cvar x (TypeVarType alpha) | (x, alpha) <- zip xs alphas ])
--           loc expr0 -- (TypeVarType beta)
--   let expr0' = substs (map Var args) xs expr'          
--   return (TupleType (map (apply delta) (map TypeVarType alphas))
--          , exprTy, delta, TupleAlternative args expr0')

-- Data constructor alternative
-- typesynthAlt_ gti gamma loc (Alternative con args expr) = do
--   case lookupConFromDataTypeInfo gti con loc of
--     ((locvars,tyvars,argtys,datatypename):_) ->
--       if length argtys==length args
--       then do
--         ls <- lift $ replicateM (length locvars) freshExistsLocationVar
--         alphas <- lift $ replicateM (length tyvars) freshExistsTypeVar
--         xs <- lift $ replicateM (length args) freshVar

--         let substLoc = zip locvars (map LocVar ls)
--         let substTy = zip tyvars (map TypeVarType alphas)

--         let substedArgtys = map (doSubst substTy . doSubstLoc substLoc) argtys

--         let expr0 = substs (map Var xs) args expr
        
--         (exprTy, gamma', expr') <-
--           typesynthExpr gti
--             (gamma >++ map CLExists ls >++ map CExists alphas 
--                    >++ map (uncurry cvar) (zip xs substedArgtys))
--                loc expr0 

--         let expr0' = substs (map Var args) xs expr'

--         return (ConType datatypename
--                   (map (lapply gamma') (map LocVar ls))
--                   (map (apply gamma') (map TypeVarType alphas))
--                , exprTy, gamma', Alternative con args expr0')

--       else throwError $ "[TypeInf] typesynthAlt: invalid arg length: " ++ con ++ show args

--     [] -> throwError $ "[TypeInf] typesynthAlt: constructor not found" ++ con


-- | Type application synthesising
--   typeapplysynth Γ loc A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth :: GlobalTypeInfo -> Context -> Location -> Type -> Expr
   -> TIMonad (Type, Location, Context, Expr -> Expr)
typeapplysynth gti gamma loc typ e = traceNS "typeapplysynth" (nolib gamma, loc, typ, e) $
  checkwftype gamma typ $
  case typ of
    -- ForallApp
    TypeAbsType alphas a -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- lift $ replicateM (length alphas) freshExistsTypeVar
      (typ', loc0, delta, g)
        <- typeapplysynth gti (gamma >++ map CExists alphas') loc
                     (typeSubsts (map TypeVarType alphas') alphas a) e
      return (typ', loc0, delta,
              g . \f -> singleTypeApp $
                         TypeApp f (Just . apply delta $ typ)
                           (map (apply delta) (map TypeVarType alphas')))

    -- ForallApp: Not allowed without any explicit location applications
    -- LForall l a -> do
    --   -- Do alpha conversion to avoid clashes
    --   l' <- lift $ freshLVar
    --   typeapplysynth (gamma >: CLExists l') loc
    --                  (locSubst (UnknownExists l') l a)
    --                  e

    -- alpha^App
    TypeVarType alpha
     | cExists alpha -> do  -- TExists alpha
      alpha1 <- lift $ freshExistsTypeVar
      alpha2 <- lift $ freshExistsTypeVar
      l      <- lift $ freshExistsLocationVar
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
      return (TypeVarType alpha2, loc', delta,
              \f -> App f (Just . apply delta $ typ) e' (Just $ lapply delta $ loc'))

    -- ->App
    FunType a loc' c -> do
      (delta, e') <- typecheckExpr gti gamma loc e a
      return (c, loc', delta,
              \f -> App f (Just . apply delta $ typ) e' (Just $ lapply delta $ loc'))


    _ -> throwError $ "typeapplysynth: don't know what to do with: "
              ++ pretty (gamma, loc, typ, e)


-- | Location application synthesising
--   locapplysynth Γ loc A loc0 = (C, Δ) <=> Γ |- A . loc0 =>> C -| Δ
locsapplysynth :: GlobalTypeInfo -> Context -> Location -> Type -> [Location]
  -> TIMonad (Type, Context, Expr -> Expr)
locsapplysynth gti gamma loc typ locs0 = traceNS "locsapplysynth" (nolib gamma, loc, typ, locs0) $
  checkwftype gamma typ $
  case typ of
    -- LForall LocApp
    LocAbsType ls a ->  -- Todo: what happens when |locs0| != |ls|?
      return (locSubsts locs0 ls a, gamma, \f -> LocApp f (Just typ) locs0)

    -- TForall LocApp
    TypeAbsType alphas a -> do
      -- Do alpha conversion to avoid clashes
      alphas' <- lift $ replicateM (length alphas) freshExistsTypeVar
      (typ', delta, g) <-
        locsapplysynth gti (gamma >++ map CExists alphas') loc
                     (typeSubsts (map TypeVarType alphas') alphas a) locs0
      return (typ', delta,
              g . \f -> singleTypeApp $
                          TypeApp f (Just . apply delta $ typ)
                            (map (apply delta) (map TypeVarType alphas')))

    -- alpha^: Not allowed because alpha^ is a monomorphic type variable!

    _ -> throwError $ "locsapplysynth: don't know what to do with: "
               ++ pretty (gamma, loc, typ, locs0)

-- | Print some debugging info
traceNS :: (Pretty a, Pretty b) => String -> a -> TIMonad b -> TIMonad b
traceNS f args x = do
  flag <- gets debug
  ilevel <- gets indent
  let ind = replicate (ilevel * 3) ' '
  log flag ind $ do
    modify $ \s -> s {indent = ilevel + 1}
    res <- x
    modify $ \s -> s {indent = ilevel}
    log_ flag ind res $ return res
  where
    log True  ind x = trace (ind ++ f ++ pretty args) x
    log False ind x = x

    log_ True  ind res x = trace (ind ++ "=" ++ pretty res) $ x
    log_ False ind res x = x

