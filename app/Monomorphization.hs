module Monomorphization(mono) where

import Location

import Type
import Expr
import Literal
import Prim
import BasicLib

import Data.List (lookup)
import Control.Monad.State

-- | TODO
--    1. Build pairs for libraries

mono :: Monad m => GlobalTypeInfo -> [TopLevelDecl] -> m [TopLevelDecl]
mono gti toplevelDecls = return toplevelDecls

-- | Type monomorphization

monoType :: Type -> Type
monoType (TypeVarType a) = TypeVarType a
monoType (TupleType tys) = TupleType $ map monoType tys
monoType (FunType ty1 loc ty2) = FunType (monoType ty1) loc (monoType ty2)
monoType (TypeAbsType alphas ty) = TypeAbsType alphas (monoType ty)
monoType (LocAbsType ls ty) =
  foldl (\ ty0 l -> TupleType [ locSubst clientLoc l ty0
                              , locSubst serverLoc l ty0 ]) ty ls
monoType (ConType c locs tys) = ConType c locs (map monoType tys)

-- | Term monomorphization

monoExpr :: Location -> Expr -> NameGen Expr

monoExpr loc (Var x) = return (Var x)

monoExpr loc (TypeAbs xs expr) = do
  mono_expr <- monoExpr loc expr
  return $ TypeAbs xs mono_expr

monoExpr loc (LocAbs ls expr) =
  foldM (\ expr0 l -> do
     mono_c <- monoExpr loc (locExprSubst clientLoc l expr0)
     mono_s <- monoExpr loc (locExprSubst serverLoc l expr0)
     return $ Tuple [ mono_c, mono_s ]
  ) expr ls

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
    f bindingDecls0 (Binding istop x ty bexpr)
      | isRec x bexpr = do
          recx <- freshName
          argunit <- freshName
          let mono_ty = monoType ty
          mono_bexpr <- monoExpr loc bexpr
          let funty = FunType unit_type loc mono_ty
          let app_recx_unit = App (Var recx) (Just funty) (Lit UnitLit) (Just loc)
          return (bindingDecls0 ++ [ Binding istop recx funty
                                       (Abs [(argunit, Just unit_type, loc)]
                                          (subst app_recx_unit recx mono_bexpr))
                                   , Binding istop x mono_ty app_recx_unit ] )

      | otherwise = do
          mono_bexpr <- monoExpr loc bexpr
          let mono_ty = monoType ty
          return (bindingDecls0 ++ [ Binding istop x mono_ty mono_bexpr ])

monoExpr loc (Case expr maybeTy alts) = do
  mono_expr <- monoExpr loc expr
  mono_alts <- mapM f alts
  let mono_maybety = fmap monoType maybeTy
  return $ Case mono_expr mono_maybety mono_alts
  where
    f (TupleAlternative xs altExpr) = do
      mono_altExpr <- monoExpr loc altExpr
      return $ TupleAlternative xs mono_altExpr

    f (Alternative c xs altExpr) = do
      mono_altExpr <- monoExpr loc altExpr
      return $ Alternative c xs mono_altExpr

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
  let mono_maybeTy = fmap monoType maybeTy
  foldM f mono_expr locs
  where
    f mono_expr0 (Location loc_name)
      | loc_name == clientLocName = return mono_expr0  -- Todo!!
      | loc_name == serverLocName = return mono_expr0

-- | A state monad for generating fresh names

data MonoState = MonoState
  { recNames :: [ExprVar]
  }

initialMonoState = MonoState
  { recNames = map ("mono$"++) namelist
  }
  where
    namelist = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State MonoState a

evalNameGen :: NameGen a -> a
evalNameGen = flip evalState initialMonoState

-- | Create a fresh variable
freshName :: NameGen ExprVar
freshName = do
  vvs <- gets recNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s {recNames = vs}
      return v
    [] -> error "No fresh variable can be created."


