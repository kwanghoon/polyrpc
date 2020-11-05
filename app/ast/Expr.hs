{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Expr(Expr(..), ExprVar, AST(..), BindingDecl(..), DataTypeDecl(..)
  , initEnv
  , TopLevelDecl(..), TypeConDecl(..), Alternative(..)
  , TypeInfo, ConTypeInfo, BindingTypeInfo, DataTypeInfo
  , GlobalTypeInfo(..), Env(..)
  , lookupConstr, lookupCon, lookupDataTypeName, lookupPrimOpType
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

type ExprVar = String

--
lookupDataTypeName gti x = [info | (y,info) <- _dataTypeInfo gti, x==y]

lookupCon tycondecls con =
  [tys | (conname, tys) <- tycondecls, con==conname]


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
  , (NeqPrimOp, (["l"], [], [bool_type, bool_type], bool_type))
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

--
-- recursive = "$rec"


-- isRecName :: String -> Bool

-- isRecName name = reverse (take 4 (reverse name)) == recursive


-- isRec :: String -> Expr -> Bool

-- isRec name (Var x) = name==x

-- isRec name (TypeAbs tyvars expr) = isRec name expr

-- isRec name (LocAbs locvars expr) = isRec name expr

-- isRec name (Abs xTyLocs expr) =
--   let (xs,tys,locs) = unzip3 xTyLocs in
--   if name `elem` xs then False
--   else isRec name expr

-- isRec name (Let bindingDecls expr) =
--   let xTyExprs = [(x,ty,expr) | Binding istop x ty expr<-bindingDecls]
--       (xs,tys, exprs) = unzip3 xTyExprs
--   in
--   if name `elem` xs then False
--   else or (isRec name expr : map (isRec name) exprs)

-- isRec name (Case expr casety [TupleAlternative xs alt_expr]) =
--   isRec name expr || if name `elem` xs then False else isRec name alt_expr

-- isRec name (Case expr casety alts) =
--   isRec name expr
--   || or (map (\(Alternative cname xs alt_expr) ->
--                 if name `elem` xs then False else isRec name alt_expr) alts)

-- isRec name (App expr maybefunty arg maybloc) = isRec name expr || isRec name arg

-- isRec name (TypeApp expr maybefunty tys) = isRec name expr

-- isRec name (LocApp expr maybefunty locs) = isRec name expr

-- isRec name (Tuple exprs) = or (map (isRec name) exprs)

-- isRec name (Prim op locs tys exprs) = or (map (isRec name) exprs)

-- isRec name (Lit lit) = False

-- isRec name (Constr cname locs tys exprs argtys) = or (map (isRec name) exprs)

-----
instance Pretty Expr where
  bpretty d expr = case expr of
    Var v       -> bpretty d v
    TypeAbs vs e -> showParen (d > abs_prec) $
      showTyVars vs . showString ". " . bpretty abs_prec e
    LocAbs ls e -> showParen (d > abs_prec) $
      showLocVars ls . showString ". " . bpretty abs_prec e
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
      showString "end"
      where
         fb (Binding istop x ty e) =
           showString x . showString " : " .
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
        fa (Alternative c xs e) =
          showString c . showString " " .
          showVars xs . showString " -> " .
          bpretty 0 e 
        fa (TupleAlternative xs e) =
          showTuple xs . showString " -> ".
          bpretty 0 e
          
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
      showString " " . showLocs tys .
      foldl (\f e -> f . showString " " . bpretty (app_prec +1) e) (\x -> x) es
    Lit lit -> showString (show lit)
    Constr c locs tys es argtys ->
      showString c .
      showString " " . showLocs locs .
      showString " " . showLocs tys .
      foldl (\f e -> f . showString " " . bpretty (app_prec +1) e) (\x -> x) es
    where
      abs_prec  = 1
      app_prec  = 10
      anno_prec = 1

      
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
