{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Location where

import Data.Set(Set)
import qualified Data.Set as S

import Text.JSON.Generic

import Naming
import Pretty

data Location =
    Location String
  | LocVar LocationVar
  deriving (Eq, Read, Show, Typeable, Data)

equalLoc (Location x) (Location y) = x==y
equalLoc (LocVar x) (LocVar y) = x==y
equalLoc _ _ = False

equalLocs [] [] = True
equalLocs (l1:locs1) (l2:locs2) = equalLoc l1 l2 && equalLocs locs1 locs2
equalLocs _ _ = False

type LocationVar = String

-- unifyLocations [] [] = Just []
-- unifyLocations (loc1:locs1) (loc2:locs2) =
--   case unifyLocation loc1 loc2 of
--     Nothing -> Nothing
--     Just subst1 ->
--       case unifyLocations (map (doSubst subst1) locs1) (map (doSubst subst1) locs2) of
--         Nothing -> Nothing
-- 	Just subst2 -> Just (subst1 ++ subst2)

-- unifyLocation (Location s1) (Location s2) =
--   if s1==s2 then Just [] else Nothing
-- unifyLocation (Location s) (LocVar x) = Just [(x, Location s)]
-- unifyLocation (LocVar x) (Location s) = Just [(x, Location s)]
-- unifyLocation (LocVar x) (LocVar y) =
--   if ==y then Just [] else Just [(x, LocVary)]

-- Predefined location names
clientLoc = Location clientLocName
serverLoc = Location serverLocName

clientLocName = "client"
serverLocName = "server"

isClient (Location str) = str == clientLocName
isClient _ = False

isServer (Location str) = str == serverLocName
isServer _ = False

--
knownLocations = [clientLocName, serverLocName]

isLocationVar s = s `elem` knownLocations

locOrVar :: String -> Location
locOrVar s
  | s `elem` knownLocations = Location s
  | otherwise               = LocVar s

--
doSubstLocOverLoc :: String -> Location -> Location -> Location

doSubstLocOverLoc x loc (Location name) = Location name
doSubstLocOverLoc x loc (LocVar y)
  | x == y = loc
  | otherwise = LocVar y


locSubstOverLoc loc x loc0 = doSubstLocOverLoc x loc loc0

doSubstLocOverLocs [] loc0 = loc0
doSubstLocOverLocs ((x,loc):substLoc) loc0 =
  doSubstLocOverLocs substLoc (doSubstLocOverLoc x loc loc0)
  
-- Pretty
instance Pretty Location where
  bpretty _ (Location locstr) = showString locstr
  bpretty d (LocVar lvar)
    | clExists lvar = showString $ "∃"++ lvar
    | otherwise     = showString lvar


--
-- | The free location variables in a location
freeLVarsIn :: Location -> Set LocationVar
freeLVarsIn loc = case loc of
  Location _ -> mempty
  LocVar l   -> S.singleton l

  
