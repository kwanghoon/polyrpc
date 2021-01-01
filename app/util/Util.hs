module Util where

allUnique [] = []
allUnique (x:xs) =
  if elem x xs then [x] else allUnique xs
