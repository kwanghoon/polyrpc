module CSSubst where

import Location
import Prim
import Literal
import CSType
import CSExpr

----------------
-- Substitutions
----------------

--
elim x subst = [(y,e) | (y,e)<-subst, y/=x]

elims xs subst = foldl (\subst0 x0 -> elim x0 subst0) subst xs


--
doSubstExpr :: [(String,Value)] -> Expr -> Expr

doSubstExpr subst (ValExpr v) = ValExpr (doSubstValue subst v)

doSubstExpr subst (Let bindingDecls expr) =
  -- let bindingDecls1 =
  --      map (\(Binding istop x ty expr) ->
  --             Binding istop x ty (doSubstExpr (elim x subst) expr)) bindingDecls

  --     elimed_subst = elims (map (\(Binding _ x _ _) -> x) bindingDecls) subst

  --     expr1 = doSubstExpr elimed_subst expr
  -- in Let bindingDecls1 expr1
  let (subst1, bindingDecls1) =
         foldl (\ (subst0, binds0) (Binding istop x ty expr) ->
            let subst1 = elim x subst0 in
                (subst1, binds0 ++ [Binding istop x ty (doSubstExpr subst1 expr)])
         ) (subst, []) bindingDecls
  in Let bindingDecls1 (doSubstExpr subst1 expr)          

doSubstExpr subst (Case v casety [TupleAlternative xs expr]) =
  let subst1 = elims xs subst
  in  Case (doSubstValue subst v) casety
        [TupleAlternative xs (doSubstExpr subst1 expr)]

doSubstExpr subst (Case v casety alts) =
  Case (doSubstValue subst v) casety
     (map (\(Alternative cname xs expr) ->
            let subst1 = elims xs subst
            in  Alternative cname xs (doSubstExpr subst1 expr)) alts)

doSubstExpr subst (App v funty arg) =
  App (doSubstValue subst v) funty (doSubstValue subst arg)

doSubstExpr subst (TypeApp v funty tyargs) =
  TypeApp (doSubstValue subst v) funty tyargs

doSubstExpr subst (LocApp v funty locargs) =
  LocApp (doSubstValue subst v) funty locargs

doSubstExpr subst (Prim op locs tys vs) = Prim op locs tys (map (doSubstValue subst) vs)



--
doSubstValue :: [(String,Value)] -> Value -> Value

doSubstValue subst (Var x) =
  case [v | (y,v) <- subst, x==y] of
    (v:_) -> v
    []    -> (Var x)

doSubstValue subst (Lit lit) = (Lit lit)

doSubstValue subst (Tuple vs) = Tuple (map (doSubstValue subst) vs)

doSubstValue subst (Constr cname locs tys vs argtys) =
  Constr cname locs tys (map (doSubstValue subst) vs) argtys

doSubstValue subst (Closure vs fvtys (CodeName fname locs tys) recf) =
  Closure (map (doSubstValue subst) vs) fvtys (CodeName fname locs tys) recf

doSubstValue subst (TypeAbs tyvars expr recf) =
  TypeAbs tyvars (doSubstExpr subst expr) recf

doSubstValue subst (UnitM v) = UnitM (doSubstValue subst v)

doSubstValue subst (BindM bindingDecls expr) =
  -- let bindingDecls1 =
  --        (map (\(Binding istop x ty bexpr) ->
  --               let subst1 = elim x subst
  --               in  Binding istop x ty (doSubstExpr subst1 bexpr))) bindingDecls

  --     elimed_subst = elims (map (\(Binding _ x _ _) -> x) bindingDecls) subst

  --     expr1 = doSubstExpr elimed_subst expr
  -- in  BindM bindingDecls1 expr1
  let (subst1, bindingDecls1) =
        foldl (\ (subst0, binds0) (Binding istop x ty expr) ->
           let subst1 = elim x subst0 in
             (subst1, binds0 ++ [Binding istop x ty (doSubstExpr subst1 expr)])
        ) (subst, []) bindingDecls
  in  BindM bindingDecls1 (doSubstExpr subst1 expr)

doSubstValue subst (Req f funty arg) =
  Req (doSubstValue subst f) funty (doSubstValue subst arg)

doSubstValue subst (Call f funty arg) =
  Call (doSubstValue subst f) funty (doSubstValue subst arg)

doSubstValue subst (GenApp loc f funty arg) =
  GenApp loc (doSubstValue subst f) funty (doSubstValue subst arg)

doSubstValue subst (Addr i) = Addr i

--doSubstValue subst v = error $ "[doSubstValue] Unexpected: " ++ show v


--
doSubstLocExpr :: [(String,Location)] -> Expr -> Expr

doSubstLocExpr substLoc (ValExpr v) = ValExpr (doSubstLocValue substLoc v)

doSubstLocExpr substLoc (Let bindingDecls expr) =
  let bindingDecls1 =
       map (\(Binding istop x ty bexpr) ->
              Binding istop x
               (doSubstLoc substLoc ty)
                 (doSubstLocExpr substLoc bexpr)) bindingDecls

  in  Let bindingDecls1 (doSubstLocExpr substLoc expr)

doSubstLocExpr substLoc (Case v casety [TupleAlternative xs expr]) =
  Case (doSubstLocValue substLoc v) (doSubstLoc substLoc casety)
    [TupleAlternative xs (doSubstLocExpr substLoc expr)]

doSubstLocExpr substLoc (Case v casety alts) =
  Case (doSubstLocValue substLoc v) (doSubstLoc substLoc casety)
    (map (\(Alternative cname xs expr) ->
            Alternative cname xs (doSubstLocExpr substLoc expr)) alts)

doSubstLocExpr substLoc (App v funty arg) =
  App (doSubstLocValue substLoc v)
        (doSubstLoc substLoc funty)
          (doSubstLocValue substLoc arg)

doSubstLocExpr substLoc (TypeApp v funty tyargs) =
  TypeApp (doSubstLocValue substLoc v)
        (doSubstLoc substLoc funty)
          (map (doSubstLoc substLoc) tyargs)

doSubstLocExpr substLoc (LocApp v funty locargs) =
  LocApp (doSubstLocValue substLoc v)
        (doSubstLoc substLoc funty)
          (map (doSubstLocOverLocs substLoc) locargs)

doSubstLocExpr substLoc (Prim op locs tys vs) =
  Prim op
    (map (doSubstLocOverLocs substLoc) locs)
      (map (doSubstLoc substLoc) tys)
        (map (doSubstLocValue substLoc) vs)


--
doSubstLocValue :: [(String,Location)] -> Value -> Value

doSubstLocValue substLoc (Var x) = Var x

doSubstLocValue substLoc (Lit lit) = Lit lit

doSubstLocValue substLoc (Tuple vs) = Tuple (map (doSubstLocValue substLoc) vs)

doSubstLocValue substLoc (Constr cname locs tys vs argtys) =
  Constr cname
        (map (doSubstLocOverLocs substLoc) locs)
          (map (doSubstLoc substLoc) tys)
            (map (doSubstLocValue substLoc) vs)
              (map (doSubstLoc substLoc) argtys)

doSubstLocValue substLoc (Closure vs fvtys (CodeName f locs tys) recf) =
  Closure (map (doSubstLocValue substLoc) vs)
    (map (doSubstLoc substLoc) fvtys )
    (CodeName f (map (doSubstLocOverLocs substLoc) locs) (map (doSubstLoc substLoc) tys))
    recf

doSubstLocValue substLoc (TypeAbs tyvars expr recf) =
  TypeAbs tyvars (doSubstLocExpr substLoc expr) recf

doSubstLocValue substLoc (UnitM v) = UnitM (doSubstLocValue substLoc v)

doSubstLocValue substLoc (BindM bindingDecls expr) =
  let bindingDecls1 =
         (map (\(Binding istop x ty bexpr) ->
            Binding istop x
              (doSubstLoc substLoc ty)
                 (doSubstLocExpr substLoc bexpr))) bindingDecls
  in  BindM bindingDecls1 (doSubstLocExpr substLoc expr)

doSubstLocValue substLoc (Req f funty arg) =
  Req (doSubstLocValue substLoc f)
        (doSubstLoc substLoc funty)
          (doSubstLocValue substLoc arg)

doSubstLocValue substLoc (Call f funty arg) =
  Call (doSubstLocValue substLoc f)
         (doSubstLoc substLoc funty)
           (doSubstLocValue substLoc arg)

doSubstLocValue substLoc (GenApp loc f funty arg) =
  GenApp (doSubstLocOverLocs substLoc loc)
           (doSubstLocValue substLoc f)
             (doSubstLoc substLoc funty)
             (doSubstLocValue substLoc arg)

doSubstLocValue substLoc (Addr i) = Addr i

--
doSubstTyExpr :: [(String,Type)] -> Expr -> Expr

doSubstTyExpr substTy (ValExpr v) = ValExpr (doSubstTyValue substTy v)

doSubstTyExpr substTy (Let bindingDecls expr) =
  let bindingDecls1 =
        map (\(Binding istop x ty expr) ->
               Binding istop x (doSubst substTy ty) (doSubstTyExpr substTy expr)) bindingDecls

  in  Let bindingDecls1 (doSubstTyExpr substTy expr)

doSubstTyExpr substTy (Case v casety [TupleAlternative xs expr]) =
  Case (doSubstTyValue substTy v) (doSubst substTy casety)
    [TupleAlternative xs (doSubstTyExpr substTy expr)]

doSubstTyExpr substTy (Case v casety alts) =
  Case (doSubstTyValue substTy v) (doSubst substTy casety)
    (map (\ (Alternative cname xs expr) ->
            Alternative cname xs (doSubstTyExpr substTy expr)) alts)

doSubstTyExpr substTy (App v funty arg) =
  App (doSubstTyValue substTy v) (doSubst substTy funty) (doSubstTyValue substTy arg)

doSubstTyExpr substTy (TypeApp v funty tyargs) =
  TypeApp (doSubstTyValue substTy v) (doSubst substTy funty) (map (doSubst substTy) tyargs)

doSubstTyExpr substTy (LocApp v funty locargs) =
  LocApp (doSubstTyValue substTy v) (doSubst substTy funty) locargs

doSubstTyExpr substTy (Prim op locs tys vs) =
  Prim op locs (map (doSubst substTy) tys) (map (doSubstTyValue substTy) vs)

--
doSubstTyValue :: [(String,Type)] -> Value -> Value


doSubstTyValue substTy (Var x) = (Var x)

doSubstTyValue substTy (Lit lit) = Lit lit

doSubstTyValue substTy (Tuple vs) = Tuple (map (doSubstTyValue substTy) vs)

doSubstTyValue substTy (Constr cname locs tys vs argtys) =
  Constr cname locs
     (map (doSubst substTy) tys)
       (map (doSubstTyValue substTy) vs)
         (map (doSubst substTy) argtys)

doSubstTyValue substTy (UnitM v) = UnitM (doSubstTyValue substTy v)

doSubstTyValue substTy (Closure vs fvtys (CodeName fname locs tys) recf) =
  Closure (map (doSubstTyValue substTy) vs)
          (map (doSubst substTy) fvtys)
          (CodeName fname locs (map (doSubst substTy) tys))
          recf

doSubstTyValue substTy (TypeAbs tyvars expr recf) =
  let substTy' = [ (alpha,ty) | (alpha,ty) <- substTy, not $ alpha `elem` tyvars ] in
  TypeAbs tyvars (doSubstTyExpr substTy' expr) recf

doSubstTyValue substTy (BindM bindingDecls expr) =
  let bindingDecls1 =
        map (\ (Binding istop x ty bexpr) ->
               Binding istop x (doSubst substTy ty) (doSubstTyExpr substTy bexpr)) bindingDecls
  in  BindM bindingDecls1 (doSubstTyExpr substTy expr)


doSubstTyValue substTy (Req f funty arg) =
  Req (doSubstTyValue substTy f) (doSubst substTy funty) (doSubstTyValue substTy arg)

doSubstTyValue substTy (Call f funty arg) =
  Call (doSubstTyValue substTy f) (doSubst substTy funty) (doSubstTyValue substTy arg)

doSubstTyValue substTy (GenApp loc f funty arg) =
  GenApp loc (doSubstTyValue substTy f) (doSubst substTy funty) (doSubstTyValue substTy arg)

doSubstTyValue substTy (Addr i) = Addr i

--
