{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving #-}
-- | Some helpers for workingw ith contexts
module Context where

import Data.Maybe
import Control.Applicative
import Data.Monoid
import Data.Semigroup

import Location
import Type
import Expr
-- import Pretty

--------------------------------------------------------------------------------
data ContextKind = Complete | Incomplete

-- | Context elements, indexed by their kind: Complete or Incomplete.
--   Only Incomplete contexts can have unsolved existentials.
data ContextElem :: ContextKind -> * where
  CForall        :: TypeVar -> ContextElem a          -- ^ alpha
  CVar           :: ExprVar -> Type -> ContextElem a  -- ^ x : A
  CExists        :: TypeVar -> ContextElem Incomplete -- ^ alpha^
  CExistsSolved  :: TypeVar -> Type -> ContextElem a  -- ^ alpha^ = tau
  CMarker        :: TypeVar -> ContextElem a          -- ^ |> alpha^

  CLForall       :: LocationVar -> ContextElem a             -- ^ l
  CLExists       :: LocationVar -> ContextElem Incomplete    -- ^ l^
  CLExistsSolved :: LocationVar -> Location -> ContextElem a -- ^ l^ = loc
  CLMarker       :: LocationVar -> ContextElem a             -- ^ |> l^
deriving instance Eq (ContextElem a)
deriving instance Show (ContextElem a)

--
existential = '^'

cExists str  = exists str

clExists str = exists str

exists str   = last str == existential

newtype GContext a   = Context [ContextElem a]
type CompleteContext = GContext Complete
type Context         = GContext Incomplete

-- | Snoc
(>:) :: GContext a -> ContextElem a -> GContext a
Context gamma >: x = Context $ x : gamma

-- | Context & list of elems append
(>++) :: GContext a -> [ContextElem a] -> GContext a
gamma >++ elems = gamma <> context elems

context :: [ContextElem a] -> GContext a
context = Context . reverse

dropMarker :: ContextElem a -> GContext a -> GContext a
dropMarker m (Context gamma) = Context $ tail $ dropWhile (/= m) gamma

breakMarker :: ContextElem a -> GContext a -> (GContext a, GContext a)
breakMarker m (Context xs) = let (r, _:l) = break (== m) xs in (Context l, Context r)

singleoutMarker :: ContextElem a -> GContext a -> GContext a
singleoutMarker m (Context gamma) = 
  let (Context l, Context r) = breakMarker m (Context gamma) in (Context (l++r))

instance Monoid (GContext a) where
  mempty = Context []
  mappend (Context gamma) (Context delta) = Context (delta ++ gamma)

instance Semigroup (GContext a) where
  (Context gamma) <> (Context delta) = Context (delta ++ gamma)

--------------------------------------------------------------------------------
existentials :: Context -> [TypeVar]
existentials (Context gamma) = aux =<< gamma
  where aux (CExists alpha)         = [alpha]
        aux (CExistsSolved alpha _) = [alpha]
        aux _                       = []

lexistentials :: Context -> [LocationVar]
lexistentials (Context gamma) = aux =<< gamma
  where aux (CLExists l)           = [l]
        aux (CLExistsSolved l loc) = [l]
        aux  _                     = []

unsolved :: Context -> [TypeVar]
unsolved (Context gamma) = [alpha | CExists alpha <- gamma]

lunsolved :: Context -> [LocationVar]
lunsolved (Context gamma) = [l | CLExists l <- gamma]

vars :: Context -> [ExprVar]
vars (Context gamma) = [x | CVar x _ <- gamma]

foralls :: Context -> [TypeVar]
foralls (Context gamma) = [alpha | CForall alpha <- gamma]

lforalls :: Context -> [LocationVar]
lforalls (Context gamma) = [l | CLForall l <- gamma]

markers :: Context -> [TypeVar]
markers (Context gamma) = [alpha | CMarker alpha <- gamma]

lmarkers :: Context -> [LocationVar]
lmarkers (Context gamma) = [l | CLMarker l <- gamma]

-- -- | Well-formedness of locations
-- --   locwf Γ loc <=> Γ |- loc
locwf :: Context -> Location -> Bool
locwf gamma loc = case loc of
  Location s -> True
  LocVar l -> 
    if clExists l
    then l `elem` lexistentials gamma
    else l `elem` lforalls gamma

-- | Well-formedness of types
--   typewf Γ A <=> Γ |- A
typewf :: Context -> Type -> Bool
typewf gamma typ = case typ of
  -- UvarWF
  TypeVarType alpha -> alpha `elem` foralls gamma
  -- EvarWF and SolvedEvarWF
--  TExists alpha -> alpha `elem` existentials gamma
  -- 
  TupleType ts -> and $ map (typewf gamma) ts
  -- ArrowWF
  FunType a loc b -> typewf gamma a && typewf gamma b && locwf gamma loc
  -- ForallWF
  TypeAbsType alphas a -> typewf (appendCtx gamma CForall alphas) a
  -- LForallWF
  LocAbsType ls a -> typewf (appendCtx gamma CLForall ls) a
  --
  ConType c ls tys -> and (map (typewf gamma) tys) && and (map (locwf gamma) ls)


appendCtx gamma f []             = gamma
appendCtx gamma f (alpha:alphas) =
  appendCtx (gamma >: f alpha) f alphas

-- -- | Well-formedness of contexts
-- --   wf Γ <=> Γ ctx
wf :: Context -> Bool
wf (Context gamma) = case gamma of
  -- EmptyCtx
  [] -> True
  c:cs -> let gamma' = Context cs in wf gamma' && case c of
    -- UvarCtx
    CForall alpha -> alpha `notElem` foralls gamma'
    -- VarCtx
    CVar x a -> x `notElem` vars gamma' && typewf gamma' a
    -- EvarCtx
    CExists alpha -> alpha `notElem` existentials gamma'
    -- SolvedEvarCtx
    CExistsSolved alpha tau -> alpha `notElem` existentials gamma'
                            && typewf gamma' tau
    -- MarkerCtx
    CMarker alpha -> alpha `notElem` markers gamma'
                  && alpha `notElem` existentials gamma'

    -- CLForall
    CLForall l -> l `notElem` lforalls gamma'

    -- CLExists
    CLExists l -> l `notElem` lexistentials gamma'

    -- CLExistsSolved
    CLExistsSolved l loc -> l `notElem` lexistentials gamma'
                         && locwf gamma' loc

    -- CLMarker
    CLMarker l -> l `notElem` lmarkers gamma'
               && l `notElem` lexistentials gamma'


-- Assert-like functionality to make sure that contexts and types are
-- well-formed
checkwf :: Context -> x -> x
checkwf gamma x | wf gamma  = x
                | otherwise = error $ "Malformed context: " -- ++ pretty gamma -- Todo!!

checkwftype :: Context -> Type -> x -> x
checkwftype gamma a x | typewf gamma a = checkwf gamma x
                      | otherwise      = error $ "Malformed type: "
                                       -- ++ pretty (a, gamma)  -- Todo!!

checkwfloc :: Context -> Location -> x -> x
checkwfloc gamma a x | locwf gamma a = checkwf gamma x
                     | otherwise     = error $ "Malformed location: "
                                     -- ++ pretty (a, gamma) -- Todo!!

-- | findSolved (ΓL,α^ = τ,ΓR) α = Just τ
findSolved :: Context -> TypeVar -> Maybe Type
findSolved (Context gamma) v = listToMaybe [t | CExistsSolved v' t <- gamma, v == v']

-- | findVarType (ΓL,x : A,ΓR) x = Just A
findVarType :: Context -> ExprVar -> Maybe Type
findVarType (Context gamma) v = listToMaybe [t | CVar v' t <- gamma, v == v']

-- | findLSolved (ΓL,l^ = τ,ΓR) l = Just τ
findLSolved :: Context -> LocationVar -> Maybe Location
findLSolved (Context gamma) l = listToMaybe [loc | CLExistsSolved l' loc <- gamma, l == l']

-- | solve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
solve :: Context -> TypeVar -> Type -> Maybe Context
solve gamma alpha tau | typewf gammaL tau = Just gamma'
                      | otherwise         = Nothing
  where (gammaL, gammaR) = breakMarker (CExists alpha) gamma
        gamma' = gammaL >++ [CExistsSolved alpha tau] <> gammaR

-- | lsolve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
lsolve :: Context -> LocationVar -> Location -> Maybe Context
lsolve gamma l loc | locwf gammaL loc = Just gamma'
                   | otherwise        = Nothing
   where (gammaL, gammaR) = breakMarker (CLExists l) gamma
         gamma' = gammaL >++ [CLExistsSolved l loc] <> gammaR

-- | insertAt (ΓL,c,ΓR) c Θ = ΓL,Θ,ΓR
insertAt :: Context -> ContextElem Incomplete -> Context -> Context
insertAt gamma c theta = gammaL <> theta <> gammaR
  where (gammaL, gammaR) = breakMarker c gamma

-- | apply Γ A = [Γ]A
apply :: Context -> Type -> Type
apply gamma typ = case typ of
  TypeVarType v     ->
    if cExists v 
      then maybe (TypeVarType v) (apply gamma) $ findSolved gamma v
      else TypeVarType v
  TupleType ts      -> TupleType (map (apply gamma) ts)
  FunType t1 loc t2 -> apply gamma t1 `FunType` lapply gamma loc $ apply gamma t2
  TypeAbsType v t   -> TypeAbsType v (apply gamma t)
  LocAbsType l t    -> LocAbsType l (apply gamma t)
  ConType c ls tys  -> ConType c (map (lapply gamma) ls) (map (apply gamma) tys)

-- | lapply Γ loc = [Γ]loc
lapply :: Context -> Location -> Location
lapply gamma loc = case loc of
  Location s -> loc
  LocVar l ->
    if clExists l 
    then maybe (LocVar l) (\loc->loc) $ findLSolved gamma l
    else LocVar l
    
-- | ordered Γ α β = True <=> Γ[α^][β^]
ordered :: Context -> TypeVar -> TypeVar -> Bool
ordered gamma alpha beta =
  let gammaL = dropMarker (CExists beta) gamma
   in alpha `elem` existentials gammaL

-- | lordered Γ α β = True <=> Γ[α^][β^]
lordered :: Context -> LocationVar -> LocationVar -> Bool
lordered gamma l1 l2 =
  let gammaL = dropMarker (CLExists l2) gamma
   in l1 `elem` lexistentials gammaL
      
