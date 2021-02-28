module Monomorphization(mono) where

import Location

import Type
import Expr
import Literal
import Prim

import Data.List (lookup)
import Control.Monad.State


-- | The monomorphization translation

-- Todo: Remove the unnecessary codes
--   - no library name list
--   - no datatype instantiations w.r.t. locations
--   - no library name instantiations w.r.t. locations
--   - no location name mangling

mono :: Monad m => GlobalTypeInfo -> [TopLevelDecl] -> [BasicLibType] -> m (GlobalTypeInfo, [TopLevelDecl], [BasicLibType])
mono gti toplevelDecls basicLib = do
  let libs      = [ l | l@(LibDeclTopLevel _ _) <- toplevelDecls ]
  let binds     = [ b | b@(BindingTopLevel _)   <- toplevelDecls ]
  let datatypes = [ d | d@(DataTypeTopLevel _)  <- toplevelDecls ]

  let libNames  = [ x | LibDeclTopLevel x _ <- libs ]
  
  let (mono_basicLib, mono_toplevelDecls) =
        evalNameGen libNames
          (do let mono_basicLib = []
              -- mono_basicLib <-
              --   mapM (\ (x,ty,expr) -> do
              --            let mono_ty = monoType ty
              --            mono_expr <- monoExpr clientLoc expr
              --            return (x, mono_ty, mono_expr) ) basicLib

              mono_toplevelDecls <-
                foldM (\ mono_tops top -> do
                          mono_top <- monoToplevel (Location clientLocName) top
                          return $ mono_tops ++ mono_top) []
                  ( datatypes ++
                    [ BindingTopLevel (Binding True x ty expr)  -- | Report the changed size
                    | (x,ty,expr) <- basicLib ] ++              -- | (Comment these two lines!)
                    binds )
                
              return (mono_basicLib, mono_toplevelDecls))

  (mono_bindingDecls, mono_datatypeDecls) <- splitTopLevelDecls mono_toplevelDecls
  mono_typeInfo     <- collectDataTypeDecls mono_datatypeDecls
  mono_dataTypeInfo <- collectDataTypeInfo  mono_datatypeDecls
  mono_conTypeInfo  <- elabConTypeDecls     mono_datatypeDecls
  
  let mono_basicLibTypeInfo = [(x,mono_ty) | (x,mono_ty,_) <- mono_basicLib]

  let mono_gti = GlobalTypeInfo
              { _typeInfo        = mono_typeInfo
              , _conTypeInfo     = mono_conTypeInfo
              , _dataTypeInfo    = mono_dataTypeInfo
              , _bindingTypeInfo = mono_basicLibTypeInfo }
              
  return (mono_gti, mono_toplevelDecls, mono_basicLib)

-- | Toplevel declaration monomorphization

monoToplevel :: Location -> TopLevelDecl -> NameGen [TopLevelDecl]
monoToplevel loc (BindingTopLevel bindingDecl) = do
  mono_bindingDecls <- monoBindingDecl loc bindingDecl
  return $ map BindingTopLevel $ mono_bindingDecls

monoToplevel loc (DataTypeTopLevel d@(DataType _ ls _ _)) =
  return $ [ DataTypeTopLevel dtDecl
           | dtDecl <- mkPair d ls [] ]
  where
    mkPair d _ _ = [d]
    
    -- mkPair d [] locs = [ monoDataTypeDecl d locs ]
    -- mkPair d (l:ls) locs =
    --   mkPair d ls (locs ++ [clientLoc]) ++ mkPair d ls (locs ++ [serverLoc])
    
    -- monoDataTypeDecl (DataType d ls alphas typeconDecls) locs =
    --   DataType (nameWithLocs d locs) (monoLocs ls) alphas
    --     (map (monoTypeConDecl locs ls) typeconDecls)

    -- monoTypeConDecl locs ls (TypeCon c tys) =
    --   TypeCon (nameWithLocs c locs) (map monoType $ map (locSubsts locs ls) tys)

monoToplevel loc (LibDeclTopLevel x ty) = do
  let binding = Binding True (mkMonoLibName x) (monoType ty) (mkPair x ty)
  return $ [ LibDeclTopLevel x ty
           , BindingTopLevel binding
           ]
  where
    mkPair x (LocAbsType ls ty) = mkPair' x ls []  --Assume either LocAbsType or not
    mkPair x ty = Var x

    mkPair' x [] locs = LocApp (Var x) (Just ty) locs
    mkPair' x (l:ls) locs =
      Tuple [ mkPair' x ls (locs ++ [clientLoc])
            , mkPair' x ls (locs ++ [serverLoc])
            ]
      
monoBindingDecl :: Location -> BindingDecl -> NameGen [BindingDecl]
monoBindingDecl loc (Binding istop x ty bexpr)
  | isRec x bexpr = do
      recx <- freshName
      argunit <- freshName
      let mono_ty = monoType ty
      mono_bexpr <- monoExpr loc (subst (Var recx) x bexpr)
      let funty = FunType unit_type loc mono_ty
      let app_recx_unit = App (Var recx) (Just funty) (Lit UnitLit) (Just loc)
      return [ Binding istop recx funty
               (Abs [(argunit, Just unit_type, loc)]
                (subst app_recx_unit recx mono_bexpr))
             , Binding istop x mono_ty app_recx_unit ]
        
  | otherwise = do
      mono_bexpr <- monoExpr loc bexpr
      let mono_ty = monoType ty
      return [ Binding istop x mono_ty mono_bexpr ]


-- | Type monomorphization

monoType :: Type -> Type
monoType (TypeVarType a) = TypeVarType a
monoType (TupleType tys) = TupleType $ map monoType tys
monoType (FunType ty1 loc ty2) = FunType (monoType ty1) loc (monoType ty2)
monoType (TypeAbsType alphas ty) = TypeAbsType alphas (monoType ty)
monoType (LocAbsType ls ty) = f ls ty
  where
    f [l] ty = TupleType [
        monoType (locSubst clientLoc l ty)
      , monoType (locSubst serverLoc l ty) ]
    f (l:ls) ty = TupleType [
        monoType (locSubst clientLoc l (LocAbsType ls ty))
      , monoType (locSubst serverLoc l (LocAbsType ls ty))  ]
monoType (ConType c locs tys) = ConType (nameWithLocs c locs) (monoLocs locs) (map monoType tys)

-- | Term monomorphization

monoExpr :: Location -> Expr -> NameGen Expr

monoExpr loc (Var x) = do
  b <- isLib x
  if not b
    then return (Var x)
    else return (Var x) -- (Var $ mkMonoLibName x)
  

monoExpr loc (TypeAbs xs expr) = do
  mono_expr <- monoExpr loc expr
  return $ TypeAbs xs mono_expr

monoExpr loc (LocAbs ls expr) = f ls expr
  where
    f [l] expr = do
      mono_c <- monoExpr loc (locExprSubst clientLoc l expr)
      mono_s <- monoExpr loc (locExprSubst serverLoc l expr)
      return $ Tuple [ mono_c, mono_s ]
    f (l:ls) expr = do
      mono_c <- monoExpr loc (locExprSubst clientLoc l (LocAbs ls expr))
      mono_s <- monoExpr loc (locExprSubst serverLoc l (LocAbs ls expr))
      return $ Tuple [ mono_c, mono_s ]

monoExpr loc0 (Abs xTyLocs expr) = do
  let loc = case last xTyLocs of (_, _, loc) -> loc
  mono_expr <- monoExpr loc expr
  return $ Abs (map f xTyLocs) mono_expr
  where
    f (x, maybety, loc) = (x, fmap monoType maybety, loc)

monoExpr loc (Let bindingDecls expr) = do
  mono_bindingDecls <- foldM f [] bindingDecls
  mono_expr <- monoExpr loc expr
  return $ Let mono_bindingDecls mono_expr
  where
    f bindingDecls0 binding = do
      bindings <- monoBindingDecl loc binding
      return $ bindingDecls0 ++ bindings
      
monoExpr loc (Case expr maybeTy alts) = do
  mono_expr <- monoExpr loc expr
  mono_alts <- mapM f alts
  let mono_maybety = fmap monoType maybeTy
  return $ Case mono_expr mono_maybety mono_alts
  where
    locs = case maybeTy of
             Just (ConType d locs tys) -> locs
      
    f (TupleAlternative xs altExpr) = do
      mono_altExpr <- monoExpr loc altExpr
      return $ TupleAlternative xs mono_altExpr

    f (Alternative c xs altExpr) = do
      mono_altExpr <- monoExpr loc altExpr
      return $ Alternative (nameWithLocs c locs) xs mono_altExpr

monoExpr loc (App expr maybeTy argExpr maybeLoc) = do
  mono_expr <- monoExpr loc expr
  mono_argExpr <- monoExpr loc argExpr
  let mono_maybeTy = fmap monoType maybeTy
  return $ App mono_expr mono_maybeTy mono_argExpr maybeLoc

monoExpr loc (TypeApp expr maybeTy tys) = do
  mono_expr <- monoExpr loc expr
  let mono_maybeTy = fmap monoType maybeTy
  let mono_tys = map monoType tys
  return $ TypeApp mono_expr mono_maybeTy mono_tys

monoExpr loc (LocApp expr maybeTy locs) = do
  mono_expr <- monoExpr loc expr
  foldM f mono_expr locs
  where
    mono_maybeTy = fmap monoType maybeTy
    
    f mono_expr0 (Location loc_name)
      | loc_name == clientLocName = mkFst mono_expr0 mono_maybeTy
      | loc_name == serverLocName = mkSnd mono_expr0 mono_maybeTy

monoExpr loc (Tuple exprs) = do
  mono_exprs <- mapM (monoExpr loc) exprs
  return $ Tuple mono_exprs

monoExpr loc (Prim op locs tys exprs) = do
  mono_exprs <- mapM (monoExpr loc) exprs
  return $ Prim op locs (map monoType tys) mono_exprs

monoExpr loc (Lit lit) = return $ Lit lit

monoExpr loc (Constr c locs tys exprs argTys) = do
  mono_exprs <- mapM (monoExpr loc) exprs
  return $
    Constr (nameWithLocs c locs) (monoLocs locs) (map monoType tys)
      mono_exprs (map monoType argTys)

mkFst :: Expr -> Maybe Type -> NameGen Expr
mkFst expr maybeTy = do
  x <- freshName
  y <- freshName
  return $ Case expr maybeTy [TupleAlternative [x,y] (Var x)]

mkSnd :: Expr -> Maybe Type -> NameGen Expr
mkSnd expr maybeTy = do
  x <- freshName
  y <- freshName
  return $ Case expr maybeTy [TupleAlternative [x,y] (Var y)]


-- | A state monad for generating fresh names

data MonoState = MonoState
  { recNames :: [ExprVar]
  , libNames :: [ExprVar]
  }

initialMonoState _libNames = MonoState
  { recNames = map ("mono$"++) namelist
  , libNames = _libNames
  }
  where
    namelist = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State MonoState a

evalNameGen :: [ExprVar] -> NameGen a -> a
evalNameGen libNames = flip evalState (initialMonoState libNames)

-- | Create a fresh variable
freshName :: NameGen ExprVar
freshName = do
  vvs <- gets recNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s {recNames = vs}
      return v
    [] -> error "No fresh variable can be created."

isLib :: ExprVar -> NameGen Bool
isLib name = do
  libs <- gets libNames
  return $ name `elem` libs

-- |

infixMonoName = "$mono$"

mkMonoLibName x = x ++ infixMonoName

monoLocs locs = locs -- []

nameWithLocs x locs = x

-- nameWithLocs x []   = x
-- nameWithLocs x locs = nameWithLocs' (x ++ "$") locs
--   where
--     nameWithLocs' x [] = x
--     nameWithLocs' x (Location a : locs) =
--       nameWithLocs' (x ++ "_" ++ a) locs
--     -- nameWithLocs' x (LocVar a : locs) =
--     --   nameWithLocs' (x ++ "_error:" ++ a) locs
