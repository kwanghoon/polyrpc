module Report (reportSize, reportCloSize) where

import qualified Expr as SE
import qualified CSExpr as TE

reportSize :: [SE.TopLevelDecl] -> Int
reportSize toplevels = sizeToplevels toplevels

-- | Program size

size (SE.Var _) = 1
size (SE.TypeAbs _ expr) = size expr
size (SE.LocAbs locs expr) = 1 + length locs - 1 + size expr
size (SE.Abs xMaybeTyLocs expr) = 1 + length xMaybeTyLocs - 1 + size expr
size (SE.Let binds expr) = 1 + sizeBinds binds + size expr
size (SE.Case expr _ alts) = 1 + size expr + sizeAlts alts
size (SE.App f _ arg _) = 1 + size f + size arg
size (SE.TypeApp expr _ _) = 1 + size expr
size (SE.LocApp expr _ locs) = 1 + size expr + length locs - 1
size (SE.Tuple exprs) = 1 + sizeExprs exprs
size (SE.Prim op locs _ exprs) = 1 + length locs - 1 + sizeExprs exprs
size (SE.Lit _) = 1
size (SE.Constr s locs _ exprs _) = 1 + length locs - 1 + sizeExprs exprs

sizeBinds [] = 0
sizeBinds (SE.Binding _ x _ expr : binds) = 1 + size expr + sizeBinds binds

sizeAlts [] = 0
sizeAlts (SE.Alternative c xs expr : alts) = 1 + size expr + sizeAlts alts
sizeAlts (SE.TupleAlternative xs expr : alts) = 1 + size expr + sizeAlts alts

sizeExprs [] = 0
sizeExprs (expr : exprs) = size expr + sizeExprs exprs

sizeToplevels :: [SE.TopLevelDecl] -> Int
sizeToplevels [] = 0
sizeToplevels (SE.BindingTopLevel bind:toplevels) = sizeBinds [bind] + sizeToplevels toplevels
sizeToplevels (_:toplevels) = sizeToplevels toplevels

-- | Closure size
reportCloSize :: TE.FunctionStore -> (Int, Int, [(Int,Int)])  -- only locs, locs+fvs, list
reportCloSize funStore = ( sum $ map fst sizes, sum $ map fst sizes ++ map snd sizes, sizes )
  where sizes = cloSize funStore
        

cloSize funStore = cloFunMap (TE._clientstore funStore) ++ cloFunMap (TE._serverstore funStore)

cloFunMap [] = []
cloFunMap ((f,(_,TE.Code locs _ fvs _)):funMap) = [(length locs, length fvs)] ++ cloFunMap funMap

