{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Runtime where

import Literal
import Prim
import Location

import qualified Data.Aeson as DA
import Control.Monad.Trans.State.Lazy
import Control.Monad.IO.Class
import qualified Data.Map as Map
import Text.JSON.Generic
import Text.JSON.Pretty

import GHC.Generics

-- | Expressions

data Expr =
--    ValExpr Value
  -- Compile-time value
    Var String
    
  -- Runtime value
  | Lit Literal
  | Tuple [Value]
  | Constr String [Value]
  | Closure [Value] CodeName [String] -- values mixed with location values

  -- Runtime value
  | Addr Integer
  
  -- Monadic value
  | UnitM Value
  | BindM [BindingDecl] Expr
  | Req Value Value           -- Todo: Replace Req,Call,GenApp with proper exprs
  | Call Value Value
  | GenApp Value Value Value  -- ARGS: Location fun arg

  -- Expression
  | Let [BindingDecl] Expr
  | Case Value [Alternative]  -- including pi_i (V)
  | App Value Value
--  | TypeApp Value Type [Type]
--  | LocApp Value [Location]
  | Prim PrimOp [Value] [Value]
  deriving (Read, Show, Typeable, Data, Generic)

instance DA.FromJSON PrimOp
instance DA.ToJSON PrimOp

instance DA.FromJSON Expr
instance DA.ToJSON Expr

data Alternative =
    Alternative String [String] Expr
  | TupleAlternative [String] Expr
  deriving (Read, Show, Typeable, Data, Generic)

instance DA.FromJSON Alternative
instance DA.ToJSON Alternative

data BindingDecl =
    Binding Bool String Expr    -- isTop?
    deriving (Read, Show, Typeable, Data, Generic)

instance DA.FromJSON BindingDecl
instance DA.ToJSON BindingDecl


-- | Values

type Value = Expr

-- data Value =
--   -- Compile-time value
--     Var String
    
--   -- Runtime value
--   | Lit Literal
--   | Tuple [Value]
--   | Constr String [Value]
--   | Closure [Value] CodeName [String] -- values mixed with location values

--   -- Runtime value
--   | Addr Integer
--   deriving (Read, Show, Typeable, Data, Generic)

-- instance DA.FromJSON Value
-- instance DA.ToJSON Value

data CodeName =
    CodeName String    -- fname (no location values and no types)
  deriving (Read, Show, Typeable, Data, Generic)

instance DA.FromJSON CodeName
instance DA.ToJSON CodeName


-----------------------------
-- | For static function map
-----------------------------

data Code =
    Code [String] OpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)
    deriving (Read, Show, Typeable, Data, Generic)

data OpenCode =
    CodeAbs [String] Expr -- normal or location value argument
    deriving (Read, Show, Typeable, Data, Generic)
    
type FunctionMap = [(String, Code)]

data FunctionStore = FunctionStore
   { _clientstore :: FunctionMap
   , _serverstore :: FunctionMap
   }

-----------------------------
-- | For runtime function map
-----------------------------

type Env = [(String, Value)]

data RuntimeCode =
    RuntimeCode [String] RuntimeOpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)
    
data RuntimeOpenCode =
    RuntimeCodeAbs [String] (Env -> Value -> RuntimeM Value) -- normal or location value argument

type RuntimeFunctionMap = [(String, RuntimeCode)]


-- Constructor names
reqName = "REQ"

callName = "CALL"

unitName = "UNIT"

-- send and receive
send :: Value -> RuntimeM ()
send v = do
  (mem,_send,_receive) <- get
  liftIO $ _send v
  return ()

receive :: RuntimeM Value
receive = do
  (mem,_send,_receive) <- get
  v <- liftIO _receive
  return v

-- JSON
toJsonString :: Value -> String
toJsonString v = render $ pp_value $ toJSON v

-- Apply
apply :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
apply funMap clo@(Closure freeVals (CodeName f) optrecf) w =  -- Tofix: optrecf !!
  case [ code | (g, code) <- funMap, f == g ] of
    (RuntimeCode fvars (RuntimeCodeAbs [_] action) :_) ->
       let env = zip fvars freeVals ++
                 case optrecf of
                   [recf] -> [(recf,clo)]
                   _ -> []
       in  action env w
    (RuntimeCode fvars (RuntimeCodeAbs xs action) :_) ->
      error $ "apply: not a single argument in CodeAbs: " ++ show xs
    [] -> error $ "apply: not found in funMap: " ++ f

req :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
req funMap f arg = do
  send $ Constr reqName [f, arg]
  loop_req funMap

call :: RuntimeFunctionMap -> Value -> Value -> RuntimeM Value
call funMap f arg = do
  send $ Constr callName [f, arg]
  loop_call funMap

loop_req :: RuntimeFunctionMap -> RuntimeM Value   -- A hack: Used RuntimeFunctionMap instead of ()
loop_req funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return $ UnitM v
      
    Constr "CALL" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_req funMap

loop_call :: RuntimeFunctionMap -> RuntimeM Value
loop_call funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return $ UnitM v
      
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_call funMap

loop_server :: RuntimeFunctionMap -> RuntimeM ()
loop_server funMap = do
  x <- receive
  case x of
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_server funMap

-- | Memory

data Mem = Mem { _new :: Integer, _map :: Map.Map Addr Value }

type Addr = Integer

initMem = Mem { _new=1, _map=Map.empty }

allocMem :: Value -> Mem -> (Addr, Mem)
allocMem v mem =
  let next = _new mem
      addrVals = _map mem
  in  (next, mem { _new=next+1, _map=Map.insert next v addrVals })

readMem :: Addr -> Mem -> Value
readMem addr mem =
  case Map.lookup addr (_map mem) of
   Just v -> v
   Nothing -> error $ "[readMem] Not found: " ++ show addr

writeMem :: Addr -> Value -> Mem -> Mem
writeMem addr v mem = mem { _map= Map.insert addr v (_map mem) }

type RuntimeState = (Mem, Value -> IO (), IO Value)

type RuntimeM = StateT RuntimeState IO

--
prim :: PrimOp -> [Value] -> [Value] -> RuntimeM Value
prim op locvals argvals = do
  (mem,_send,_receive) <- get
  (v, mem') <- liftIO $ calc op locvals argvals mem
  put (mem',_send,_receive)
  return v
  
  where
    -- ToDo: Fix the duplicate code!
    
    -- calc :: PrimOp -> [Location] -> [Type] -> [Value] -> Mem -> IO (Value, Mem)
    calc :: PrimOp -> [Value] -> [Value] -> Mem -> IO (Value, Mem)

    -- calc MkRecOp locs [Closure vs codename [], Lit (StrLit f)] mem =
    --   return (Closure vs fvtys codename [f], mem)

    -- calc MkRecOp locs vs mem =
    --   error $ "[MkRecOp]: Unexpected: "
    --               ++ show locs ++ " " ++ show vs

    calc PrimRefCreateOp [loc1] [v] mem =
      let (addr, mem1) = allocMem v mem in return (Addr addr, mem1)

    calc PrimRefCreateOp locs vs mem =
      error $ "[PrimOp] PrimRefCreateOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimRefReadOp [loc1] [Addr addr] mem = return (readMem addr mem, mem)

    calc PrimRefReadOp locs vs mem =
      error $ "[PrimOp] PrimRefReadOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimRefWriteOp [loc1] [Addr addr,v] mem =
      return (Lit UnitLit, writeMem addr v mem)

    calc PrimRefWriteOp locs vs mem =
      error $ "[PrimOp] PrimRefWriteOp: Unexpected: "
                  ++ show locs ++ " " ++ " " ++ show vs

    calc PrimReadOp [loc] [Lit (UnitLit)] mem = do
      line <- getLine
      return (Lit (StrLit line), mem)

    calc PrimPrintOp [loc] [Lit (StrLit s)] mem = do
      putStr s
      return (Lit UnitLit, mem)


    calc primop locs vs mem =
      return (Lit $ calc' primop locs (map getLit vs), mem)

      where
        getLit (Lit lit) = lit
        getLit v = error $ "[Execute] calc-getLit: what? " ++ show v

    -- Primitives
    -- calc' :: PrimOp -> [Location] -> [Type] -> [Literal] -> Literal
    calc' :: PrimOp -> [Value] -> [Literal] -> Literal

    calc' NotPrimOp [loc] [BoolLit b] = BoolLit (not b)  -- loc is the current location

    calc' OrPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x || y)

    calc' AndPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x && y)

    calc' EqStringPrimOp [loc] [StrLit x, StrLit y] = BoolLit (x==y)

    calc' EqBoolPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x==y)

    calc' EqIntPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x==y)

    calc' NeqStringPrimOp [loc] [StrLit x, StrLit y] = BoolLit (x/=y)

    calc' NeqBoolPrimOp [loc] [BoolLit x, BoolLit y] = BoolLit (x/=y)

    calc' NeqIntPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x/=y)

    calc' LtPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x<y)

    calc' LePrimOp [loc] [IntLit x, IntLit y] = BoolLit (x<=y)

    calc' GtPrimOp [loc] [IntLit x, IntLit y] = BoolLit (x>y)

    calc' GePrimOp [loc] [IntLit x, IntLit y] = BoolLit (x>=y)

    calc' AddPrimOp [loc] [IntLit x, IntLit y] = IntLit (x+y)

    calc' SubPrimOp [loc] [IntLit x, IntLit y] = IntLit (x-y)

    calc' MulPrimOp [loc] [IntLit x, IntLit y] = IntLit (x*y)

    calc' DivPrimOp [loc] [IntLit x, IntLit y] = IntLit (x `div` y)

    calc' NegPrimOp [loc] [IntLit x] = IntLit (-x)

    -- Libraries
    calc' PrimIntToStringOp [loc] [IntLit i] = StrLit (show i)

    calc' PrimConcatOp [loc] [StrLit s1, StrLit s2] = StrLit (s1++s2)

    calc' operator locs operands =
      error $ "[PrimOp] Unexpected: "
         ++ show operator ++ " " ++ show locs ++ " " ++ " " ++ show operands

-- Reading R programs
load_expr :: String -> IO Expr
load_expr fileName = do
  text <- readFile fileName
  return $ read text

load_funstore :: String -> IO FunctionMap
load_funstore fileName = do
  text <- readFile fileName
  return $ read text

-------------------------------------------------------------------------------
-- | Interpreter for the untyped expressions
-------------------------------------------------------------------------------

interpFunMap :: String -> FunctionMap -> RuntimeFunctionMap
interpFunMap myloc rFunMap = funMap
  where
    funMap = interpFunMap' myloc rFunMap funMap

    interpFunMap' myloc rFunMap funMap =
      [ (f, RuntimeCode fvvars (RuntimeCodeAbs ys action))
      | (f, (Code fvvars (CodeAbs ys expr))) <- rFunMap,
        let  action = codeAbsToPair myloc (CodeAbs ys expr)
      ]

    codeAbsToPair myloc (CodeAbs [x] expr) =
      let actionExpr = interpExpr myloc expr in
      (\env v -> actionExpr funMap (env ++ [(x,v)]))
      
    codeAbsToPair myloc (CodeAbs xs expr) =
      error $ "interpFunMap: not a single arg var: " ++ show (length xs)

interpExpr :: String -> Expr -> RuntimeFunctionMap -> Env -> RuntimeM Value
interpExpr myloc (UnitM v) = \ runtimeFunMap env -> return (UnitM v)

interpExpr myloc (BindM [Binding b x bexpr] expr) =
  let actionBexpr = interpExpr myloc bexpr
      actionExpr = interpExpr myloc expr
  in  (\ runtimeFunMap env -> do
          mValue <- actionBexpr runtimeFunMap env
          case mValue of
            UnitM bValue -> actionExpr runtimeFunMap (env ++ [(x, bValue)])
            _ -> error $ "[Runtime:interpExpr] BindM: Not UnitM: " ++ show mValue )

interpExpr myloc (BindM bindDecls expr) =
 error $ "[Runtime:interpExpr] BindM: not a single binding: " ++ show (length bindDecls)

interpExpr myloc (Req f arg) = \ runtimeFunMap env -> req runtimeFunMap f arg

interpExpr myloc (Call f arg) = \ runtimeFunMap env -> call runtimeFunMap f arg

interpExpr myloc (GenApp locval f arg) = \ runtimeFunMap env -> do
  if myloc == clientLocName then
    case locval of
      Constr fLoc [] ->
        if myloc == fLoc then apply runtimeFunMap f arg
        else req runtimeFunMap f arg
      _ -> error $ "[Runtime:interpExpr] GenApp@client: invalid location: " ++ show locval
      
  else if myloc == serverLocName then
    case locval of
      Constr fLoc [] ->
        if myloc == fLoc then apply runtimeFunMap f arg
        else call runtimeFunMap f arg
      _ -> error $ "[Runtime:interpExpr] GenApp@server: invalid location: " ++ show locval

  else error $ "[Runtime:interpExpr] GenApp: unknown location: " ++ myloc

interpExpr myloc (Let [Binding b x bexpr] expr) =
  let actionBexpr = interpExpr myloc bexpr
      actionExpr = interpExpr myloc expr
  in (\ runtimeFunMap env -> do
         bValue <- actionBexpr runtimeFunMap env
         actionExpr runtimeFunMap (env ++ [(x, bValue)]) )

interpExpr myloc (Let bindDecls expr) =
 error $ "[Runtime:interpExpr] BindM : not a single binding: " ++ show (length bindDecls)

interpExpr myloc (Case value alts) =
  let actionCaseVal = interpExpr myloc value
      actionAlts = interpAlts myloc alts
  in (\ runtimeFunMap env -> do 
         v <- actionCaseVal runtimeFunMap env
         actionCase v actionAlts runtimeFunMap env )
  where
    interpAlts myloc alts = 
      [ case alt of 
          Alternative dname xs expr -> (Just dname, xs, interpExpr myloc expr)
          TupleAlternative xs expr -> (Nothing, xs, interpExpr myloc expr)
      | alt <- alts ]

    actionCase v@(Constr cname args) actionAlts runtimeFunMap env = 
      case [ (xs, actionExpr)
           | (Just dname, xs, actionExpr) <- actionAlts, cname==dname ] of
        ((xs,actionExpr):_) 
          | length args == length xs -> 
              actionExpr runtimeFunMap (env ++ zip xs args)
          | otherwise -> error $ "[Runtime:interpExpr] case alt: arity mismatch: "
                           ++ show (length args) ++ " != " ++ show (length xs)
        [] -> error $ "[Runtime:interpExpr] case alt: no match for: " ++ show v

    actionCase v@(Tuple args) [(Nothing, xs, actionExpr)] runtimeFunMap env
      | length args == length xs = actionExpr runtimeFunMap (env ++ zip xs args)
      | otherwise = error $ "[Runtime:interpExpr] case alt: arity mismatch: "
                      ++ show (length args) ++ " != " ++ show (length xs)

    actionCase v@(Tuple args) _ runtimeFunMap env = 
      error $ "[Runtime:interpExpr] Not a single tuple aternative"

    actionCase v actionAlts runtimeFunMap env = 
      error $ "[Runtime:interpExpr] Unexpected case value: " ++ show v

interpExpr myloc (App f arg) =
  (\ runtimeFunMap env -> apply runtimeFunMap f arg)

interpExpr myloc (Prim op locvals argvals) = 
  (\ runtimeFunMap env -> prim op locvals argvals)

