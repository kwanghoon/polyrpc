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
import BasicLib
import qualified CSType as TT
import qualified CSExpr as TE
import TypeCheck
import TypeInf
import Monomorphization
import Compile
import Simpl
import Verify
import Execute
import CodeGen

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
  (gti, elab_toplevelDecls1, elab_builtinDatatypes, lib_toplevelDecls)
    <- typeInf (_flag_debug_typecheck cmd) toplevelDecls basicLib

  let elab_toplevelDecls = lib_toplevelDecls ++ elab_builtinDatatypes ++ elab_toplevelDecls1

  verbose (_flag_dump_typecheck cmd) $ putStrLn "Dumping..."
  verbose (_flag_dump_typecheck cmd) $ putStrLn $ show $ elab_toplevelDecls1

  let jsonfile = prefixOf file ++ ".json"
  print_rpc cmd jsonfile elab_toplevelDecls1

{-
  putStrLn "[Type checking]"
  (gti, elab_toplevelDecls) <- typeCheck toplevelDecls basicLib
  verbose (_flag_debug_typecheck cmd) $ putStrLn "Dumping..."
  verbose (_flag_debug_typecheck cmd) $ putStrLn $ show $ elab_toplevelDecls

  print_rpc cmd file elab_toplevelDecls
-}

  (s_gti, s_toplevelDecls, s_basicLib) <-
    if _flag_monomorphization cmd || _flag_debug_monomorphization cmd
    then do
      putStrLn "[Monomorphization]"
      (mono_gti, mono_toplevelDecls, mono_basicLib) <-
        mono gti elab_toplevelDecls basicLib

      -- verbose (_flag_debug_monomorphization cmd) $ putStrLn "Dumping..."
      -- verbose (_flag_debug_monomorphization cmd) $ putStrLn $ show $ elab_toplevelDecls1

      let jsonfile = prefixOf file ++ "_mono.json"
      verbose (_flag_debug_monomorphization cmd) $ print_rpc cmd jsonfile mono_toplevelDecls

      -- putStrLn "mono_gti"
      -- putStrLn (show mono_gti)

      return (mono_gti, mono_toplevelDecls, mono_basicLib)

    else return (gti, elab_toplevelDecls, basicLib)

  putStrLn "[Compiling]"
  (t_gti, funStore, t_expr) <- compile s_gti s_toplevelDecls s_basicLib
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

  -- Code generation for Web
  if _flag_code_gen cmd == True
  then do
    putStrLn "[Code generation]"
    let csClientFile = prefixOf file ++ "_client.cs"
    let csClientMainFile = prefixOf file ++ "_main.cs"
    let csServerFile = prefixOf file ++ "_server.cs"
    print_expr t_expr csClientMainFile
    print_funstore (TE._clientstore funStore) csClientFile
    print_funstore (TE._serverstore funStore) csServerFile
  else
    codeGen t_gti funStore t_expr

  -- Execution
  if _flag_code_gen cmd == False
  then do
    putStrLn "[Executing codes]"
    v <- execute (_flag_debug_run cmd) t_gti funStore t_expr
    verbose (_flag_debug_run cmd) $ putStrLn $ "[Result]\n" ++ show v
  else
    return ()

  -- Done!!
  putStrLn "[Success]"


--
print_rpc cmd jsonfile elab_toplevelDecls = do
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

print_expr :: TE.Expr -> String -> IO ()
print_expr expr fileName = do
  writeFile fileName $ show expr
  
print_funstore :: TE.FunctionMap -> String -> IO ()
print_funstore functionMap fileName = do
  writeFile fileName $ show functionMap

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
      , _flag_dump_typecheck :: Bool
      , _flag_monomorphization :: Bool
      , _flag_debug_monomorphization :: Bool
      , _flag_debug_compile :: Bool
      , _flag_debug_simpl :: Bool
      , _flag_debug_verify :: Bool
      , _flag_debug_run :: Bool
      , _flag_code_gen :: Bool
      , _files :: [String]
      }

initCmd =
  Cmd { _flag_print_rpc_json = False
      , _flag_print_cs_json  = False
      , _flag_print_inlined_cs_json = False
      , _flag_debug_lex = False
      , _flag_debug_parse = False
      , _flag_debug_typecheck = False
      , _flag_dump_typecheck = False
      , _flag_monomorphization = False
      , _flag_debug_monomorphization = False
      , _flag_debug_compile = False
      , _flag_debug_simpl = False
      , _flag_debug_verify = False
      , _flag_debug_run = False
      , _flag_code_gen = False
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

collect cmd ("--dump-typecheck":args) = do
  let new_cmd = cmd { _flag_dump_typecheck = True }
  collect new_cmd args

collect cmd ("--monomorphization":args) = do
  let new_cmd = cmd { _flag_monomorphization = True }
  collect new_cmd args

collect cmd ("--debug-monomorphization":args) = do
  let new_cmd = cmd { _flag_debug_monomorphization = True }
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

collect cmd ("--code-gen":args) = do
  let new_cmd = cmd { _flag_code_gen = True }
  collect new_cmd args

collect cmd (arg:args) = do
  let old_files = _files cmd
  let new_cmd = cmd { _files = old_files ++ [arg] }
  collect new_cmd args


verbose b action = if b then action else return ()

--
version = "0.2.2"
printVersion = putStrLn $ "POLYRPC, version " ++ version ++ ": http://github.com/kwanghoon/polyrpc/"
