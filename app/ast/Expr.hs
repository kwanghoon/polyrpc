{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Expr(Expr(..), ExprVar, AST(..), BindingDecl(..), DataTypeDecl(..)
  , initEnv
  , TopLevelDecl(..), TypeConDecl(..), Alternative(..)
  , TypeInfo, ConTypeInfo, BindingTypeInfo, DataTypeInfo
  , GlobalTypeInfo(..), Env(..), BasicLibType
  , lookupConstr, lookupCon, lookupDataTypeName
  , lookupConFromDataTypeInfo, lookupPrimOpType
  , mainName, primOpTypes
  , singleTypeAbs, singleLocAbs, singleAbs
  , singleTypeApp, singleLocApp
  , setTop
  , toASTExprSeq, toASTExpr
  , toASTIdSeq, toASTId
  , toASTTypeSeq, toASTType
  , toASTLocationSeq, toASTLocation
  , toASTBindingDeclSeq, toASTBindingDecl
  , toASTDataTypeDecl, toASTTopLevelDeclSeq
  , toASTTypeConDeclSeq, toASTTypeConDecl
  , toASTIdTypeLocSeq, toASTIdTypeLoc
  , toASTAlternativeSeq, toASTAlternative
  , toASTTriple, toASTLit
  , subst, substs, substs_, tyExprSubst, tyExprSubsts, locExprSubst, locExprSubsts
  , typeconOrVar, isRec
  , splitTopLevelDecls, collectDataTypeDecls, elabConTypeDecls, collectDataTypeInfo
  , builtinDatatypes
  ) where

import Location
import Prim
import Literal
import Type
-- For aeson
-- import GHC.Generics
-- import Data.Aeson
import Text.JSON.Generic
import Pretty
import Util

import Data.Char

--
data Expr =
    Var ExprVar
  | TypeAbs [String] Expr
  | LocAbs [String] Expr
  | Abs [(ExprVar, Maybe Type, Location)] Expr
  | Let [BindingDecl] Expr
  | Case Expr (Maybe Type) [Alternative]
  | App Expr (Maybe Type) Expr (Maybe Location)
  | TypeApp Expr (Maybe Type) [Type]
  | LocApp Expr (Maybe Type) [Location]
  | Tuple [Expr]
  | Prim PrimOp [Location] [Type] [Expr]
  | Lit Literal
  | Constr String [Location] [Type] [Expr] [Type]
-- For aeson
--  deriving (Show, Generic)
  deriving (Show, Typeable, Data)

--------------------------------------------------------------------
-- On location annotations:
--------------------------------------------------------------------
-- In Abs, the location is given by programmers.
-- In App, the location is inferred automatically.
-- In LocApp, the locations are given by programmers.
-- In Prim, locations in primitives except (ref), (!), and (:=) are
--    set with the current location. For (ref), (!), and (:=), the
--    location is given through LocApp by programmers.
-- In Constr, the locations are given through LocApp by programmers.
--------------------------------------------------------------------

type ExprVar = String

--
isTypeVar s = null s == False && isLower (head s)

isTypeConr s  = null s == False && isUpper (head s)

typeconOrVar s
  | isTypeVar s = TypeVarType s
  | otherwise   = ConType s [] []

--
lookupDataTypeName gti x = [info | (y,info) <- _dataTypeInfo gti, x==y]

lookupCon tycondecls con =
  [tys | (conname, tys) <- tycondecls, con==conname]

--
-- Given a constructor name, this returns its type.
--
lookupConFromDataTypeInfo :: GlobalTypeInfo -> String -> Location ->
  [([LocationVar], [ExprVar], [Type], String)]
lookupConFromDataTypeInfo gti con loc =
  [ (locvars, tyvars, tys, datatypeName)
  | (datatypeName, (locvars, tyvars, info)) <- _dataTypeInfo gti
  , (con',  tys) <- info, con==con' ]
    

--
singleTypeAbs (TypeAbs [] expr) = expr
singleTypeAbs (TypeAbs [a] expr) = TypeAbs [a] expr
singleTypeAbs (TypeAbs (a:as) expr) = TypeAbs [a] (singleTypeAbs (TypeAbs as expr))
singleTypeAbs other = other

singleLocAbs (LocAbs [] expr) = expr
singleLocAbs (LocAbs [l] expr) = LocAbs [l] expr
singleLocAbs (LocAbs (l:ls) expr) = LocAbs [l] (singleLocAbs (LocAbs ls expr))
singleLocAbs other = other

singleAbs (Abs [] expr) = expr
singleAbs (Abs [t] expr) = Abs [t] expr
singleAbs (Abs (t:ts) expr) = Abs [t] (singleAbs (Abs ts expr))
singleAbs other = other

singleTypeApp (TypeApp expr maybe []) = expr
singleTypeApp (TypeApp expr maybe [ty]) = TypeApp expr maybe [ty]
singleTypeApp (TypeApp expr maybe (ty:tys)) =
  singleTypeApp
    (TypeApp
       (TypeApp expr maybe [ty]) (skimTypeAbsType maybe) tys)
singleTypeApp other = other

skimTypeAbsType Nothing = Nothing
skimTypeAbsType (Just (TypeAbsType (tyvar:tyvars) ty)) = Just (TypeAbsType tyvars ty)
skimTypeAbsType maybe = error $ "[skimTypeAbsType]: " ++ show maybe

singleLocApp (LocApp expr maybe []) = expr
singleLocApp (LocApp expr maybe [l]) = LocApp expr maybe [l]
singleLocApp (LocApp expr maybe (l:ls)) =
  singleLocApp
     (LocApp (LocApp expr maybe [l]) (skimLocAbsType maybe) ls)
singleLocApp other = other

skimLocAbsType Nothing = Nothing
skimLocAbsType (Just (LocAbsType (locvar:locvars) ty)) = Just (LocAbsType locvars ty)
skimLocAbsType maybe = error $ "[skimLocAbsType]: " ++ show maybe

data BindingDecl =
    Binding Bool ExprVar Type Expr -- isTop?
-- For aeson
--  deriving (Show, Generic)
    deriving (Show, Typeable, Data)

setTop :: BindingDecl -> BindingDecl
setTop (Binding _ x ty expr) = Binding True x ty expr

--
-- The four forms of data type declarations supported now.
--
--  data D =                             C1 | ... | Cn
--  data D = [a1 ... ak]               . C1 | ... | Cn
--  data D = {l1 ... li}               . C1 | ... | Cn
--  data D = {l1 ... li} . [a1 ... ak] . C1 | ... | Cn
--
data DataTypeDecl =
    DataType String [LocationVar] [TypeVar] [TypeConDecl] --
    deriving (Show, Typeable, Data)

data TopLevelDecl =
    BindingTopLevel BindingDecl
  | DataTypeTopLevel DataTypeDecl
  | LibDeclTopLevel String Type
  deriving (Show, Typeable, Data)

data TypeConDecl =
   TypeCon String [Type]
   deriving (Show, Typeable, Data)

data Alternative =
    Alternative String [String] Expr
  | TupleAlternative [String] Expr
  deriving (Show, Typeable, Data)

--
-- For aeson
-- instance ToJSON Expr where
-- instance ToJSON Literal where
-- instance ToJSON PrimOp where
-- instance ToJSON BindingDecl where
-- instance ToJSON DataTypeDecl where
-- instance ToJSON TopLevelDecl where
-- instance ToJSON TypeConDecl where
-- instance ToJSON Alternative where

--
-- For type-checker

-- [(Name, Location Vars, Type Vars)]
type TypeInfo = [(String, [String], [String])]

-- [(ConName, (ConArgTypes, DTName, LocationVars, TypeVars))]
type ConTypeInfo = [(String, ([Type], String, [String], [String]))]

lookupConstr :: GlobalTypeInfo -> String -> [([Type], String, [String], [String])]
lookupConstr gti x = [z | (con, z) <- _conTypeInfo gti, x==con]


type BindingTypeInfo = [(String, Type)]

-- [ (DTName, LocationVars, TypeVars, [(ConName, ArgTypes)]) ]
type DataTypeInfo = [(String, ([String], [String], [(String,[Type])]))]

data GlobalTypeInfo = GlobalTypeInfo
       { _typeInfo :: TypeInfo
       , _conTypeInfo :: ConTypeInfo
       , _dataTypeInfo :: DataTypeInfo
       , _bindingTypeInfo :: BindingTypeInfo }
    deriving (Show, Typeable, Data)

data Env = Env
       { _locVarEnv  :: [String]
       , _typeVarEnv :: [String]
       , _varEnv     :: BindingTypeInfo }

initEnv = Env { _locVarEnv=[], _typeVarEnv=[], _varEnv=[] }

type BasicLibType = (String, Type, Expr)

-- | Built-in datatypes

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

-- | datatype manipulation functions

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
splitTopLevelDecl (LibDeclTopLevel x ty) = return ([], [])


-- 
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

--
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

--
collectDataTypeInfo :: Monad m => [DataTypeDecl] -> m DataTypeInfo
collectDataTypeInfo datatypeDecls = do
  mapM get datatypeDecls
  where get (DataType name locvars tyvars tycondecls) =
          return (name, (locvars, tyvars,map f tycondecls))
        f (TypeCon s tys) = (s,tys)


--
data AST =
    ASTExprSeq { fromASTExprSeq :: [Expr] }
  | ASTExpr    { fromASTExpr    :: Expr   }
  | ASTIdSeq   { fromASTIdSeq   :: [String] }
  | ASTId      { fromASTId      :: String }
  | ASTTypeSeq { fromASTTypeSeq :: [Type] }
  | ASTType    { fromASTType    :: Type  }
  | ASTLocationSeq { fromASTLocationSeq :: [Location] }
  | ASTLocation    { fromASTLocation    :: Location  }

  | ASTBindingDeclSeq { fromASTBindingDeclSeq :: [BindingDecl] }
  | ASTBindingDecl    { fromASTBindingDecl    :: BindingDecl  }

  | ASTDataTypeDecl { fromASTDataTypeDecl :: DataTypeDecl }

  | ASTTopLevelDeclSeq { fromASTTopLevelDeclSeq :: [TopLevelDecl] }

  | ASTTypeConDeclSeq { fromASTTypeConDeclSeq :: [TypeConDecl] }
  | ASTTypeConDecl { fromASTTypeConDecl :: TypeConDecl }

  | ASTIdTypeLocSeq { fromASTIdTypeLocSeq :: [(String,Maybe Type,Location)] }
  | ASTIdTypeLoc { fromASTIdTypeLoc :: (String,Maybe Type,Location) }

  | ASTAlternativeSeq { fromASTAlternativeSeq :: [Alternative] }
  | ASTAlternative { fromASTAlternative :: Alternative }

  | ASTLit { fromASTLit :: Literal }

  | ASTTriple { fromASTTriple :: ([String], [String], [TypeConDecl]) }

instance Show AST where
  showsPrec p _ = (++) "AST ..."

toASTExprSeq exprs = ASTExprSeq exprs
toASTExpr expr     = ASTExpr expr
toASTIdSeq   ids   = ASTIdSeq ids
toASTId   id       = ASTId id
toASTTypeSeq types = ASTTypeSeq types
toASTType ty     = ASTType ty
toASTLocationSeq locations = ASTLocationSeq locations
toASTLocation location     = ASTLocation location

toASTBindingDeclSeq bindings = ASTBindingDeclSeq bindings
toASTBindingDecl binding     = ASTBindingDecl binding

toASTDataTypeDecl datatype     = ASTDataTypeDecl datatype

toASTTopLevelDeclSeq toplevel = ASTTopLevelDeclSeq toplevel

toASTTypeConDeclSeq typecondecls = ASTTypeConDeclSeq typecondecls
toASTTypeConDecl typecondecl     = ASTTypeConDecl typecondecl

toASTIdTypeLocSeq idtypelocs = ASTIdTypeLocSeq idtypelocs
toASTIdTypeLoc idtypeloc     = ASTIdTypeLoc idtypeloc

toASTAlternativeSeq alts = ASTAlternativeSeq alts
toASTAlternative alt     = ASTAlternative alt

toASTTriple triple = ASTTriple triple

toASTLit lit     = ASTLit lit

--
mainName = "main"

--
primOpTypes :: [(PrimOp, ([String], [String], [Type], Type))]  -- (locvars, tyvars, argtys, retty)
primOpTypes =
  [

  -----------------------------------------------------------------------------------
  -- [Note] Primitives that the typechecker provide locations as the current location
  -----------------------------------------------------------------------------------

    (NotPrimOp, (["l"], [], [bool_type], bool_type))
  , (OrPrimOp,  (["l"], [], [bool_type, bool_type], bool_type))
  , (AndPrimOp, (["l"], [], [bool_type, bool_type], bool_type))
  
  , (EqStringPrimOp,  (["l"], [], [string_type, string_type], bool_type))
  , (EqBoolPrimOp,  (["l"], [], [bool_type, bool_type], bool_type))
  , (EqIntPrimOp,  (["l"], [], [int_type, int_type], bool_type))
  
  , (NeqStringPrimOp, (["l"], [], [string_type, string_type], bool_type))
  , (NeqBoolPrimOp, (["l"], [], [bool_type, bool_type], bool_type))
  , (NeqIntPrimOp, (["l"], [], [int_type, int_type], bool_type))
  
  , (LtPrimOp,  (["l"], [], [int_type, int_type], bool_type))
  , (LePrimOp,  (["l"], [], [int_type, int_type], bool_type))
  , (GtPrimOp,  (["l"], [], [int_type, int_type], bool_type))
  , (GePrimOp,  (["l"], [], [int_type, int_type], bool_type))
  , (AddPrimOp, (["l"], [], [int_type, int_type], int_type))
  , (SubPrimOp, (["l"], [], [int_type, int_type], int_type))
  , (MulPrimOp, (["l"], [], [int_type, int_type], int_type))
  , (DivPrimOp, (["l"], [], [int_type, int_type], int_type))
  , (NegPrimOp, (["l"], [], [int_type], int_type))

  , (PrimReadOp, (["l"], [], [unit_type], string_type))
  , (PrimPrintOp, (["l"], [], [string_type], unit_type))
  , (PrimIntToStringOp, (["l"], [], [int_type], string_type))
  , (PrimConcatOp, (["l"], [], [string_type,string_type], string_type))

  -----------------------------------------------------------------------------------
  -- [Note] Primitives that programmers provide locations
  -----------------------------------------------------------------------------------

  , (PrimRefCreateOp,
      let l1 = "l1" in
      let a  = "a"  in
      let tyvar_a = TypeVarType a in
      let locvar_l1 = LocVar l1 in
        ([l1], [a], [tyvar_a], ConType refType [locvar_l1] [tyvar_a]))

  , (PrimRefReadOp,
      let l1 = "l1" in
      let a  = "a"  in
      let tyvar_a = TypeVarType a in
      let locvar_l1 = LocVar l1 in
        ([l1], [a], [ConType refType [locvar_l1] [tyvar_a]], tyvar_a))

  , (PrimRefWriteOp,
     let l1 = "l1" in
     let a  = "a"  in
     let tyvar_a = TypeVarType a in
     let locvar_l1 = LocVar l1 in
        ([l1], [a], [ConType refType [locvar_l1] [tyvar_a], tyvar_a], unit_type))
  ]

lookupPrimOpType primop =
  [ (locvars, tyvars, tys,ty)
  | (primop1,(locvars, tyvars, tys,ty)) <- primOpTypes, primop==primop1]

-- | is this recursive?
isRec :: String -> Expr -> Bool

isRec name (Var x) = name==x

isRec name (TypeAbs tyvars expr) = isRec name expr

isRec name (LocAbs locvars expr) = isRec name expr

isRec name (Abs xTyLocs expr) =
  let (xs,tys,locs) = unzip3 xTyLocs in
  if name `elem` xs then False else isRec name expr

isRec name (Let bindingDecls expr) =
  or (map (\ (Binding _ x ty bexpr) -> name/=x && isRec name bexpr
  ) bindingDecls)
  || isRec name expr

  -- if name `elem` xs then False
  -- else or (isRec name expr : map (isRec name) exprs)
  -- where
  --   (xs,tys, exprs) = unzip3 [(x,ty,expr) | Binding _ x ty expr<-bindingDecls]

isRec name (Case expr casety [TupleAlternative xs alt_expr]) =
  isRec name expr || if name `elem` xs then False else isRec name alt_expr

isRec name (Case expr casety alts) =
  isRec name expr
  || or (map (\ (Alternative cname xs alt_expr) ->
                not (name `elem` xs) && isRec name alt_expr) alts)

isRec name (App expr maybefunty arg maybloc) = isRec name expr || isRec name arg

isRec name (TypeApp expr maybefunty tys) = isRec name expr

isRec name (LocApp expr maybefunty locs) = isRec name expr

isRec name (Tuple exprs) = or (map (isRec name) exprs)

isRec name (Prim op locs tys exprs) = or (map (isRec name) exprs)

isRec name (Lit lit) = False

isRec name (Constr cname locs tys exprs argtys) = or (map (isRec name) exprs)

-----
instance Pretty Expr where
  bpretty d expr = case expr of
    Var v       -> showString v
    TypeAbs vs e -> showParen (d > abs_prec) $
      showString "[" . showWithSpace vs . showString "]. " . bpretty abs_prec e
    LocAbs ls e -> showParen (d > abs_prec) $
      showString "{" . showWithSpace ls . showString "}. " . bpretty abs_prec e
    Abs varMaybeTyLocs e -> showParen (d >abs_prec) $
      showString "\\" . showVarMaybeTyLocs varMaybeTyLocs .
      showString ". " . bpretty abs_prec e
    Let bindDecls e -> showParen (d > 0) $
      showString "let { " .
      foldl (\f bindDecl ->
               f . fb bindDecl . showString "; ")
            (\x->x) (init bindDecls) .
      fb (last bindDecls) .
      showString " } " .
      bpretty 0 e .
      showString " end"
      where
         fb (Binding istop x ty e) =
           showString (x ++ " : ") .
           bpretty 0 ty . showString " = " .
           bpretty 0 e

    Case e maybeTy alts -> showParen (d > 0) $
      showString "case " .
      bpretty 0 e .
      showString " { " .
      foldl (\f alt ->
               f . fa alt . showString "; ")
            (\x->x) (init alts) .
      fa (last alts) .
      showString " } "
      where
        fa alt = bpretty 0 alt
        -- fa (Alternative c xs e) =
        --   showString c . showString " " .
        --   showVars xs . showString " -> " .
        --   bpretty 0 e 
        -- fa (TupleAlternative xs e) =
        --   showTuple xs . showString " -> ".
        --   bpretty 0 e
          
    App e1 maybeTy e2 maybeLoc -> showParen (d > app_prec) $    
      bpretty app_prec e1 . showString " " . bpretty (app_prec + 1) e2
    TypeApp e1 maybeTy tys -> showParen (d > app_prec) $
      bpretty app_prec e1 . showString " " . showTys tys
    LocApp e1 maybeTy locs -> showParen (d > app_prec) $
      bpretty app_prec e1 . showString " " . showLocs locs
    Tuple es -> showTuple es
    Prim op locs tys es -> showParen (d > 0) $
      showString (show op) .
      showString " " . showLocs locs .
      showString " " . showTys tys .
      foldl (\f e -> f . showString " " . bpretty (app_prec +1) e) (\x -> x) es
    Lit lit -> showString (show lit)
    Constr c locs tys es argtys ->
      showString c .
      showString " " . showLocs locs .
      showString " " . showTys tys .
      foldl (\f e -> f . showString " " . bpretty (app_prec +1) e) (\x -> x) es
    where
      abs_prec  = 1
      app_prec  = 10
      anno_prec = 1

instance Pretty Alternative where
  bpretty d (Alternative con args expr) =
    showString con . showString " " .
    showWithSpace args . showString " -> " .
    bpretty 0 expr
    
  bpretty d (TupleAlternative args expr) =
    showString "(" . showWith "," args . showString ")"
    . showString " -> ". bpretty 0 expr

instance Pretty BindingDecl where
  bpretty d _ = showString ""
  
--     EApp e1 e2   -> showParen (d > app_prec) $
--       bpretty app_prec e1 . showString " " . bpretty (app_prec + 1) e2
--     ELocApp e loc   -> showParen (d > app_prec) $
--       bpretty app_prec e . showString " " . bpretty (app_prec + 1) loc
--     EAnno e t -> showParen (d > anno_prec) $
--       bpretty (anno_prec + 1) e . showString " : " . bpretty anno_prec t
--     where
--       abs_prec  = 1
--       app_prec  = 10
--       anno_prec = 1

-- | subst e' x e = [e'/x]e
subst :: Expr -> ExprVar -> Expr -> Expr
subst e' x (Var y)
  | x == y = e'
  | otherwise = Var y

subst e' x (TypeAbs xs e) = TypeAbs xs (subst e' x e)

subst e' x (LocAbs xs e) = LocAbs xs (subst e' x e)

subst e' x (Abs vTyLocs e)
  | x `elem` (fmap fst3 vTyLocs) = Abs vTyLocs e
  | otherwise = Abs vTyLocs (subst e' x e)
  where
    fst3 (x,y,z) = x

subst e' x (Let bindingDecls e) = Let (f bindingDecls) (g e)
  where
    f [] = []
    f (Binding b y ty e : binds)
      | x == y    = Binding b y ty e : binds
      | otherwise = Binding b y ty (subst e' x e) : f binds

    g e
      | x `elem` [ y | (Binding _ y _ _) <- bindingDecls ] = e
      | otherwise = subst e' x e

subst e' x (Case e maybety alts) =
  Case (subst e' x e) maybety (fmap f alts)
  where
    f (Alternative c xs e) = Alternative c xs (subst e' x e)
    f (TupleAlternative xs e) = TupleAlternative xs (subst e' x e)

subst e' x (App e1 maybety e2 maybeloc) =
  App (subst e' x e1) maybety (subst e' x e2) maybeloc

subst e' x (TypeApp e maybety tys) = TypeApp (subst e' x e) maybety tys

subst e' x (LocApp e maybety locs) = LocApp (subst e' x e) maybety locs

subst e' x (Tuple es) = Tuple (fmap (subst e' x) es)

subst e' x (Prim p locs tys es) = Prim p locs tys (fmap (subst e' x) es)

subst e' x (Lit lit) = Lit lit

subst e' x (Constr c locs tys es argtys) =
  Constr c locs tys (fmap (subst e' x) es) argtys

substs es' xs' e = 
  foldl (\ e0 (e',x) -> subst e' x e0) e (zip es' xs')

substs_ exs e = let (es, xs) = unzip exs in substs es xs e

-- | tyExprSubst ty alpha e = [ty/alpha]e
tyExprSubst :: Type -> TypeVar -> Expr -> Expr
tyExprSubst ty' alpha (Var y) = Var y

tyExprSubst ty' alpha (TypeAbs xs e)
  | alpha `elem` xs = (TypeAbs xs e)
  | otherwise = TypeAbs xs (tyExprSubst ty' alpha e)

tyExprSubst ty' alpha (LocAbs xs e) = LocAbs xs (tyExprSubst ty' alpha e)

tyExprSubst ty' alpha (Abs vTyLocs e) =
  Abs (fmap ftriple vTyLocs) (tyExprSubst ty' alpha e)
  where
    ftriple (x, maybeTy, loc) =
      (x, fmap (doSubstOne alpha ty') maybeTy, loc)

tyExprSubst ty' alpha (Let bindingDecls e) =
  Let (fmap f bindingDecls) (tyExprSubst ty' alpha e)
  where
    f (Binding b x ty e) =
      Binding b x (doSubstOne alpha ty' ty) (tyExprSubst ty' alpha e)

tyExprSubst ty' alpha (Case e maybety alts) =
  Case (tyExprSubst ty' alpha e) (fmap (doSubstOne alpha ty') maybety) (fmap f alts)
  where
    f (Alternative c xs e) = Alternative c xs (tyExprSubst ty' alpha e)
    f (TupleAlternative xs e) = TupleAlternative xs (tyExprSubst ty' alpha e)

tyExprSubst ty' alpha (App e1 maybety e2 maybeloc) =
  App (tyExprSubst ty' alpha e1)
    (fmap (doSubstOne alpha ty') maybety)
      (tyExprSubst ty' alpha e2) maybeloc

tyExprSubst ty' alpha (TypeApp e maybety tys) =
  TypeApp (tyExprSubst ty' alpha e)
    (fmap (doSubstOne alpha ty') maybety)
       (fmap (doSubstOne alpha ty') tys)

tyExprSubst ty' alpha (LocApp e maybety locs) =
  LocApp (tyExprSubst ty' alpha e)
    (fmap (doSubstOne alpha ty') maybety) locs

tyExprSubst ty' alpha (Tuple es) = Tuple (fmap (tyExprSubst ty' alpha) es)

tyExprSubst ty' alpha (Prim p locs tys es) =
  Prim p locs
    (fmap (doSubstOne alpha ty') tys)
      (fmap (tyExprSubst ty' alpha) es)

tyExprSubst ty' alpha (Lit lit) = Lit lit

tyExprSubst ty' alpha (Constr c locs tys es argtys) =
  Constr c locs
    (fmap (doSubstOne alpha ty') tys)
      (fmap (tyExprSubst ty' alpha) es)
        (fmap (doSubstOne alpha ty') argtys)

tyExprSubsts tys' alphas' e = 
  foldl (\ e0 (ty',alpha) -> tyExprSubst ty' alpha e0) e (zip tys' alphas')

-- | locExprSubst loc l e = [loc/l]e
locExprSubst loc' l (Var v) = Var v

locExprSubst loc' l (TypeAbs vs e) = TypeAbs vs (locExprSubst loc' l e)

locExprSubst loc' l (LocAbs vs e)
  | l `elem` vs = LocAbs vs e
  | otherwise = LocAbs vs (locExprSubst loc' l e)
  
locExprSubst loc' l (Abs vTyLocs e) =
  Abs (fmap ftriple vTyLocs) (locExprSubst loc' l e)
  where
    ftriple (x, maybeTy, loc) =
      (x, fmap (locSubst loc' l) maybeTy, locSubstOverLoc loc' l loc)

locExprSubst loc' l (Let bindingDecls e) =
  Let (fmap f bindingDecls) (locExprSubst loc' l e)
  where
    f (Binding b x ty e) =
      Binding b x (locSubst loc' l ty) (locExprSubst loc' l e)
      

locExprSubst loc' l (Case e maybeTy alts) =
  Case (locExprSubst loc' l e) (fmap (locSubst loc' l) maybeTy) (fmap f alts)
  where
    f (Alternative c xs e) = Alternative c xs (locExprSubst loc' l e)
    f (TupleAlternative xs e) = TupleAlternative xs (locExprSubst loc' l e)

locExprSubst loc' l (App e1 maybeTy e2 maybeLoc) =
  App (locExprSubst loc' l e1) (fmap (locSubst loc' l) maybeTy)
    (locExprSubst loc' l e2) (fmap (locSubstOverLoc loc' l) maybeLoc)

locExprSubst loc' l (TypeApp e maybeTy tys) =
  TypeApp (locExprSubst loc' l e)
    (fmap (locSubst loc' l) maybeTy)
      (fmap (locSubst loc' l) tys)

locExprSubst loc' l (LocApp e maybeTy locs) =
  LocApp (locExprSubst loc' l e)
    (fmap (locSubst loc' l) maybeTy)
      (fmap (locSubstOverLoc loc' l) locs)

locExprSubst loc' l (Tuple es) =
  Tuple (fmap (locExprSubst loc' l) es)

locExprSubst loc' l (Prim p locs tys es) =
  Prim p
    (fmap (locSubstOverLoc loc' l) locs)
      (fmap (locSubst loc' l) tys)
         (fmap (locExprSubst loc' l) es)

locExprSubst loc' l (Lit lit) = Lit lit

locExprSubst loc' l (Constr c locs tys es argTys) =
  Constr c
    (fmap (locSubstOverLoc loc' l) locs)
      (fmap (locSubst loc' l) tys)
         (fmap (locExprSubst loc' l) es)
            (fmap (locSubst loc' l) argTys)


locExprSubsts :: [Location] -> [LocationVar] -> Expr -> Expr
locExprSubsts locs' ls e =
  foldl (\ e0 (loc', l) -> locExprSubst loc' l e0) e (zip locs' ls)

{-
  Var v -> Var v
  EUnit -> EUnit
  EAbs v loc0 e0 -> EAbs v (locLocSubst loc' l loc0) (locExprSubst loc' l e0)
  ELocAbs l0 e0 | l0 == l   -> ELocAbs l0 e0
                | otherwise -> ELocAbs l0 (locExprSubst loc' l e0)
  EApp e1 e2     -> EApp (locExprSubst loc' l e1) (locExprSubst loc' l e2)
  ELocApp e loc  -> ELocApp (locExprSubst loc' l e) (locLocSubst loc' l loc)
  EAnno e ty     -> EAnno (locExprSubst loc' l e) (locSubst loc' l ty)
-}

