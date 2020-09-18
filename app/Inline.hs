module Inline (inline) where

import Location
import Prim
import Literal
import CSType
import CSExpr

--------------------------------------------------------------------------
-- Inlining all (bound) unit values
--------------------------------------------------------------------------
-- BindM [ Binding x ty (ValExpr (UnitM v)) ] expr  ===>  expr [v/x]
--------------------------------------------------------------------------


---------------------
-- Inline CS programs
---------------------

inline :: Monad m => GlobalTypeInfo -> FunctionStore -> Expr
                     -> m (GlobalTypeInfo, FunctionStore, Expr)
inline gti funStore mainexpr = do
  funStore' <- inlineFunStore gti funStore
  mainexpr' <- inlineExpr (gti, funStore) clientLoc initEnv (MonType unit_type) mainexpr
  return (gti, funStore', mainexpr')

-------------------------
-- Inline function stores
-------------------------

type GlobalInfo = (GlobalTypeInfo, FunctionStore)

inlineFunStore :: Monad m => GlobalTypeInfo -> FunctionStore -> m FunctionStore
inlineFunStore gti funStore = do
  let clientFunStore = _clientstore funStore
  let serverFunStore = _serverstore funStore

  clientFunStore' <- mapM (inlineFnCode gti clientLoc funStore) clientFunStore
  serverFunStore' <- mapM (inlineFnCode gti serverLoc funStore) serverFunStore

  return $ funStore{_clientstore=clientFunStore', _serverstore=serverFunStore'}


inlineFnCode :: Monad m => GlobalTypeInfo -> Location -> FunctionStore
                        -> (String, (CodeType, Code)) -> m (String, (CodeType, Code))
inlineFnCode gti loc funStore (f, (codety, code)) = do
  code' <- inlineCode (gti,funStore) loc codety code
  return (f, (codety, code'))


inlineCode gtigci loc codty code@(Code freeLocVars freeTyVars freeVars openCode) = 
  return code

inlineExpr gtigci loc env ty expr = return expr
