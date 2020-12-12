{-# LANGUAGE DeriveGeneric #-}

module Main where

import CommonParserUtil

import Token
import Lexer
import Terminal
import Parser
import qualified ParserBidi as PB
import Type
import Expr
import qualified CSType as TT
import qualified CSExpr as TE
import TypeCheck
import TypeInf
import Compile
import Simpl
import Verify
import Execute

import Text.JSON.Generic
import Text.JSON.Pretty
import Text.PrettyPrint
-- For aeson
--import qualified Data.ByteString.Lazy.Char8 as B
--import Data.Aeson.Encode.Pretty
import Data.Maybe
import System.IO
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  cmd  <- getCmd args

  let files = _files cmd

  printVersion
  mapM_ (doProcess cmd) files -- [ ((build cmd file), file) | file <- files ]

doProcess cmd file = do
  putStrLn $ "[Reading] " ++ file
  text <- readFile file

  putStrLn "[Lexing]"
  terminalList <- lexing lexerSpec text
  verbose (_flag_debug_lex cmd) $ mapM_ (putStrLn) (map terminalToString terminalList)


  -- putStrLn "[Parsing]"
  -- exprSeqAst <- parsing parserSpec terminalList
  
  putStrLn "[Parsing-Surface syntax]"
  exprSeqAst <- parsing PB.parserSpec terminalList

  verbose (_flag_debug_parse cmd) $ putStrLn "Dumping..."
  verbose (_flag_debug_parse cmd) $ putStrLn $ show $ fromASTTopLevelDeclSeq exprSeqAst

  let toplevelDecls = fromASTTopLevelDeclSeq exprSeqAst

  putStrLn "[Bidirectional type checking]"
  (gti, elab_toplevelDecls1, elab_toplevelDecls0, lib_toplevelDecls) <- typeInf toplevelDecls

  let elab_toplevelDecls = lib_toplevelDecls ++ elab_toplevelDecls0 ++ elab_toplevelDecls1
  
  verbose (_flag_debug_typecheck cmd) $ putStrLn "Dumping..."
  verbose (_flag_debug_typecheck cmd) $ putStrLn $ show $ elab_toplevelDecls1

  print_rpc cmd file elab_toplevelDecls1

{-
  putStrLn "[Type checking]"
  (gti, elab_toplevelDecls) <- typeCheck toplevelDecls
  verbose (_flag_debug_typecheck cmd) $ putStrLn "Dumping..."
  verbose (_flag_debug_typecheck cmd) $ putStrLn $ show $ elab_toplevelDecls

  print_rpc cmd file elab_toplevelDecls
-}

{-
  putStrLn "[Compiling]"
  (t_gti, funStore, t_expr) <- compile gti elab_toplevelDecls
  verbose (_flag_debug_compile cmd) $ putStrLn "Dumping...\nGlobal type information:\n"
  verbose (_flag_debug_compile cmd) $ putStrLn $ (show t_gti ++ "\n\nFunction stores:")
  verbose (_flag_debug_compile cmd) $ putStrLn $ (show funStore ++ "\n\nMain expression:")
  verbose (_flag_debug_compile cmd) $ putStrLn $ (show t_expr ++ "\n")

  print_cs cmd file funStore t_expr

  putStrLn "[Verifying after compilation]"
  verify t_gti funStore t_expr
  verbose (_flag_debug_verify cmd) $ putStrLn "[Well-typed]"

  putStrLn "[Inlining]"
  (t_gti, funStore, t_expr) <- simpl t_gti funStore t_expr
  verbose (_flag_debug_simpl cmd) $ putStrLn "Dumping...\nGlobal type information:\n"
  verbose (_flag_debug_simpl cmd) $ putStrLn $ (show t_gti ++ "\n\nFunction stores:")
  verbose (_flag_debug_simpl cmd) $ putStrLn $ (show funStore ++ "\n\nMain expression:")
  verbose (_flag_debug_simpl cmd) $ putStrLn $ (show t_expr ++ "\n")

  print_inlined_cs cmd file funStore t_expr

  putStrLn "[Verifying after inlining]"
  verify t_gti funStore t_expr
  verbose (_flag_debug_verify cmd) $ putStrLn "[Well-typed]"

  putStrLn "[Executing codes]"
  v <- execute (_flag_debug_run cmd) t_gti funStore t_expr
  verbose (_flag_debug_run cmd) $ putStrLn $ "[Result]\n" ++ show v
-}
  putStrLn "[Success]"


--
print_rpc cmd file elab_toplevelDecls = do
  let jsonfile = prefixOf file ++ ".json"
  if _flag_print_rpc_json cmd
  then do putStrLn $ "Writing to " ++ jsonfile
          writeFile jsonfile $ render
             $ pp_value $ toJSON (elab_toplevelDecls :: [TopLevelDecl])
  else return ()

print_cs cmd file funStore t_expr = do
  -- let jsonfile = prefixOf file ++ "_cs.json"
  -- if _flag_print_cs_json cmd
  -- then do putStrLn $ "Writing to " ++ jsonfile
  --         writeFile jsonfile $ render
  --            $ pp_value $ toJSON (funStore :: TE.FunctionStore, t_expr :: TE.Expr)
  -- else return ()

  if _flag_print_cs_json cmd
  then print_cs_json (prefixOf file) funStore t_expr
  else return ()

print_inlined_cs cmd file funStore t_expr = do
  if _flag_print_inlined_cs_json cmd
  then print_cs_json (prefixOf file ++ "_inlined") funStore t_expr
  else return ()

print_cs_json fileName funStore t_expr = do
  let jsonfile = fileName ++ "_cs.json"
  putStrLn $ "Writing to " ++ jsonfile
  writeFile jsonfile $ render
      $ pp_value $ toJSON (funStore :: TE.FunctionStore, t_expr :: TE.Expr)

prefixOf str = reverse (removeDot (dropWhile (/='.') (reverse str)))
  where removeDot []     = []
        removeDot (x:xs) = xs  -- x must be '.'

--
readline msg = do
  putStr msg
  hFlush stdout
  readline'

readline' = do
  ch <- getChar
  if ch == '\n' then
    return ""
  else
    do line <- readline'
       return (ch:line)

--
data Cmd =
  Cmd { _flag_print_rpc_json :: Bool
      , _flag_print_cs_json :: Bool
      , _flag_print_inlined_cs_json :: Bool
      , _flag_debug_lex :: Bool
      , _flag_debug_parse :: Bool
      , _flag_debug_typecheck :: Bool
      , _flag_debug_compile :: Bool
      , _flag_debug_simpl :: Bool
      , _flag_debug_verify :: Bool
      , _flag_debug_run :: Bool
      , _files :: [String]
      }

initCmd =
  Cmd { _flag_print_rpc_json = False
      , _flag_print_cs_json  = False
      , _flag_print_inlined_cs_json = False
      , _flag_debug_lex = False
      , _flag_debug_parse = False
      , _flag_debug_typecheck = False
      , _flag_debug_compile = False
      , _flag_debug_simpl = False
      , _flag_debug_verify = False
      , _flag_debug_run = False
      , _files = []
      }

getCmd :: Monad m => [String] -> m Cmd
getCmd args = collect initCmd args

collect :: Monad m => Cmd -> [String] -> m Cmd
collect cmd [] = return cmd
collect cmd ("--output-json":args) = do
  let new_cmd = cmd { _flag_print_rpc_json = True }
  collect new_cmd args

collect cmd ("--output-rpc-json":args) = do
  let new_cmd = cmd { _flag_print_rpc_json = True }
  collect new_cmd args

collect cmd ("--output-cs-json":args) = do
  let new_cmd = cmd { _flag_print_cs_json = True }
  collect new_cmd args

collect cmd ("--output-inlined-cs-json":args) = do
  let new_cmd = cmd { _flag_print_inlined_cs_json = True }
  collect new_cmd args

collect cmd ("--debug-lex":args) = do
  let new_cmd = cmd { _flag_debug_lex = True }
  collect new_cmd args

collect cmd ("--debug-parse":args) = do
  let new_cmd = cmd { _flag_debug_parse = True }
  collect new_cmd args

collect cmd ("--debug-typecheck":args) = do
  let new_cmd = cmd { _flag_debug_typecheck = True }
  collect new_cmd args

collect cmd ("--debug-compile":args) = do
  let new_cmd = cmd { _flag_debug_compile = True }
  collect new_cmd args

collect cmd ("--debug-simpl":args) = do
  let new_cmd = cmd { _flag_debug_simpl = True }
  collect new_cmd args

collect cmd ("--debug-verify":args) = do
  let new_cmd = cmd { _flag_debug_verify = True }
  collect new_cmd args

collect cmd ("--debug-run":args) = do
  let new_cmd = cmd { _flag_debug_run = True }
  collect new_cmd args

collect cmd (arg:args) = do
  let old_files = _files cmd
  let new_cmd = cmd { _files = old_files ++ [arg] }
  collect new_cmd args


verbose b action = if b then action else return ()

--
version = "0.1.0"
printVersion = putStrLn $ "POLYRPC, version " ++ version ++ ": http://github.com/kwanghoon/polyrpc/"
