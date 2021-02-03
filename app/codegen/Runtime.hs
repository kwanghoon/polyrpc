{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Runtime where

import Literal
import Prim

import qualified Data.Map as Map
import Text.JSON.Generic

data Value =
    Lit Literal
  | Tuple [Value]
  | Constr String [Value]
  | Closure [Value] CodeName [String] -- values mixed with location values
  deriving (Show, Typeable, Data)

data CodeName =
    CodeName String    -- fname (no location values and no types)
  deriving (Show, Typeable, Data)

data Code =
    Code [String] OpenCode --  [free var or possibley free loc var]. OpenCode  (and no alphas)

type Env = [(String, Value)]

data OpenCode =
    CodeAbs [String] (Env -> Value -> IO Value) -- normal or location value argument

type FunctionMap = [(String, Code)]


-- Constructor names
reqName = "REQ"

callName = "CALL"

unitName = "UNIT"

-- send and receive
send :: Value -> IO ()
send v = return () -- ToFix

receive :: IO Value
receive = return $ Tuple [] -- ToFix

apply :: FunctionMap -> Value -> Value -> IO Value
apply funMap clo@(Closure freeVals (CodeName f) optrecf) w =  -- Tofix: optrecf !!
  case [ code | (g, code) <- funMap, f == g ] of
    (Code fvars (CodeAbs [_] action) :_) ->
       let env = zip fvars freeVals ++
                 case optrecf of
                   [recf] -> [(recf,clo)]
                   _ -> []
       in  action env w
    (Code fvars (CodeAbs xs action) :_) ->
      error $ "apply: not a single argument in CodeAbs: " ++ show xs
    [] -> error $ "apply: not found in funMap: " ++ f

req :: FunctionMap -> Value -> Value -> IO Value
req funMap f arg = do
  send $ Constr reqName [f, arg]
  loop_req funMap

call :: FunctionMap -> Value -> Value -> IO Value
call funMap f arg = do
  send $ Constr callName [f, arg]
  loop_call funMap

loop_req :: FunctionMap -> IO Value   -- A hack: Used FunctionMap instead of ()
loop_req funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return v
      
    Constr "CALL" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_req funMap

loop_call :: FunctionMap -> IO Value
loop_call funMap = do
  x <- receive
  case x of
    Constr "UNIT" [v] ->
      return v
      
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_call funMap

loop_server :: FunctionMap -> IO Value
loop_server funMap = do
  x <- receive
  case x of
    Constr "REQ" [f, arg] -> do
      w <- apply funMap f arg
      send (Constr "UNIT" [w])
      loop_req funMap

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


--
prim :: PrimOp -> [Value] -> [Value] -> IO Value
prim op locvals argvals = return $ Tuple []  -- Tofix

-- calc :: PrimOp -> [Location] -> [Type] -> [Value] -> Mem -> IO (Value, Mem)

-- -- calc MkRecOp locs tys [Closure vs fvtys codename [], Lit (StrLit f)] mem =
-- --   return (Closure vs fvtys codename [f], mem)

-- -- calc MkRecOp locs tys vs mem =
-- --   error $ "[MkRecOp]: Unexpected: "
-- --               ++ show locs ++ " " ++ show tys ++ " " ++ show vs

-- calc PrimRefCreateOp [loc1] [ty] [v] mem =
--   let (addr, mem1) = allocMem v mem in return (Addr addr, mem1)

-- calc PrimRefCreateOp locs tys vs mem =
--   error $ "[PrimOp] PrimRefCreateOp: Unexpected: "
--               ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

-- calc PrimRefReadOp [loc1] [ty] [Addr addr] mem = return (readMem addr mem, mem)

-- calc PrimRefReadOp locs tys vs mem =
--   error $ "[PrimOp] PrimRefReadOp: Unexpected: "
--               ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

-- calc PrimRefWriteOp [loc1] [ty] [Addr addr,v] mem =
--   return (Lit UnitLit, writeMem addr v mem)

-- calc PrimRefWriteOp locs tys vs mem =
--   error $ "[PrimOp] PrimRefWriteOp: Unexpected: "
--               ++ show locs ++ " " ++ show  tys ++ " " ++ show vs

-- calc PrimReadOp [loc] [] [Lit (UnitLit)] mem = do
--   line <- getLine
--   return (Lit (StrLit line), mem)

-- calc PrimPrintOp [loc] [] [Lit (StrLit s)] mem = do
--   putStr s
--   return (Lit UnitLit, mem)


-- calc primop locs tys vs mem =
--   return (Lit $ calc' primop locs tys (map getLit vs), mem)

--   where
--     getLit (Lit lit) = lit
--     getLit v = error $ "[Execute] calc-getLit: what? " ++ show v
--                        ++ "\n  in " ++ show (Prim primop locs tys vs)

-- -- Primitives
-- calc' :: PrimOp -> [Location] -> [Type] -> [Literal] -> Literal

-- calc' NotPrimOp [loc] [] [BoolLit b] = BoolLit (not b)  -- loc is the current location

-- calc' OrPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x || y)

-- calc' AndPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x && y)

-- calc' EqStringPrimOp [loc] [] [StrLit x, StrLit y] = BoolLit (x==y)

-- calc' EqBoolPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x==y)

-- calc' EqIntPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x==y)

-- calc' NeqStringPrimOp [loc] [] [StrLit x, StrLit y] = BoolLit (x/=y)

-- calc' NeqBoolPrimOp [loc] [] [BoolLit x, BoolLit y] = BoolLit (x/=y)

-- calc' NeqIntPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x/=y)

-- calc' LtPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x<y)

-- calc' LePrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x<=y)

-- calc' GtPrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x>y)

-- calc' GePrimOp [loc] [] [IntLit x, IntLit y] = BoolLit (x>=y)

-- calc' AddPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x+y)

-- calc' SubPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x-y)

-- calc' MulPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x*y)

-- calc' DivPrimOp [loc] [] [IntLit x, IntLit y] = IntLit (x `div` y)

-- calc' NegPrimOp [loc] [] [IntLit x] = IntLit (-x)

-- -- Libraries
-- calc' PrimIntToStringOp [loc] [] [IntLit i] = StrLit (show i)

-- calc' PrimConcatOp [loc] [] [StrLit s1, StrLit s2] = StrLit (s1++s2)

-- calc' operator locs tys operands =
--   error $ "[PrimOp] Unexpected: "
--      ++ show operator ++ " " ++ show locs ++ " " ++ show tys ++ " " ++ show operands

