module Monomorphization where

import Location

import qualified Type as ST
import qualified Expr as SE
import Literal
import Prim
import BasicLib

mono :: Monad m => SE.GlobalTypeInfo -> [SE.TopLevelDecl] -> m [SE.TopLevelDecl]
mono gti toplevelDecls = return toplevelDecls


