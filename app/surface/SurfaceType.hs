{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module SurfaceType where

import Location

-- For parsing
noLocName = "$NoLoc"  -- Just to represent A -> B by A -$NoLoc-> B

getLocFromMaybe :: Maybe Location -> Location
getLocFromMaybe (Just loc) = loc 
getLocFromMaybe Nothing    = LocVar optionalLocVarName

optionalLocVarName = "l"
