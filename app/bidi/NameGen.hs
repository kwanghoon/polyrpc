-- | Name generation
module NameGen where
import Control.Monad.State

import Naming
import Location
import Type
import Expr
import Pretty

import Debug.Trace

data NameState = NameState
  { varNames  :: [ExprVar]
  , tvarNames :: [TypeVar]
  , lvarNames :: [LocationVar]
  , indent    :: Int -- This has no place here, but useful for debugging
  , debug     :: Bool
  }

-- data EVar = EVar ExprVar
-- data TVar = TVar TypeVar
-- data LVar = LVar LocationVar

initialNameState :: NameState
initialNameState = NameState
  { varNames  = map ({- EVar . -} ('$':)) namelist
  , tvarNames = map ({- TVar . -} ('\'':)) namelist
  , lvarNames = map ({- LVar . -} ("\'l_"++)) namelist
  , indent    = 0
  , debug     = False
  }
  where
    namelist = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State NameState a

evalNameGen :: NameGen a -> a
evalNameGen = flip evalState initialNameState

-- | Create a fresh variable
freshVar :: NameGen ExprVar
freshVar = do
  vvs <- gets varNames
  case vvs of
    (v:vs) -> do 
      modify $ \s -> s {varNames = vs}
      return v
    [] -> error "No fresh variable can be created."

-- | Create a fresh type variable
freshTypeVar :: NameGen TypeVar
freshTypeVar = do
  vvs <- gets tvarNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s {tvarNames = vs}
      return v
    [] -> error "No fresh type variable can be created."

freshExistsTypeVar = do
  alpha <- freshTypeVar
  return $ mkExists alpha

-- | Create a fresh location variable
freshLocationVar :: NameGen LocationVar
freshLocationVar = do
  vvs <- gets lvarNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s {lvarNames = vs}
      return v
    [] -> error "No fresh location variable can be created."

freshExistsLocationVar = do
  l <- freshLocationVar
  return $ mkExists l

setDebug :: Bool -> NameGen ()
setDebug flag = do
  modify $ \s -> s {debug = flag}
  return ()
