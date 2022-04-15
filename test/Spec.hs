module Main where

-- import ParserBidiLinksTest

-- main :: IO ()
-- main = runTestTT parserTests

import SyntaxCompletion (computeCand)
import SynCompInterface
import Test.Hspec

import Config

import Data.Maybe (isJust)
import System.IO (readFile)

spec = hspec $ do
  describe "Testing examples/exp/benchmarks" $ do
    let benchmark1 = "main : Int = if x "           -- examples/exp/benchmark1.rl
    let benchmark2 = "main : Int = if x > 1 then "  -- examples/exp/benchmark2.rl

    let config_simple = True
    
    let config =
          Configuration
            {
              config_SIMPLE       = config_simple,
              config_R_LEVEL      = 1,
              config_GS_LEVEL     = 1,
              config_DEBUG        = False,
              config_DISPLAY      = False,
              config_PRESENTATION = 0,
              config_ALGORITHM    = 3
            }
    
    it ("[Benchmark1] " ++ benchmark1) $
      do mapM_ (item benchmark1 config) [1..8]  -- Max GS level (8) for Smallbasic

    it ("[Benchmark2] " ++ benchmark2) $
      do mapM_ (item benchmark2 config) [1..8]  -- Max GS level (8) for Smallbasic

item benchmark init_config gslevel = 
      do let test_config = init_config{config_GS_LEVEL=gslevel}
         putStrLn (show test_config)
         
         configMaybe <- readConfig
         case configMaybe of
           Just config ->
             do writeConfig test_config  -- set
                results <- computeCand False benchmark "" (config_SIMPLE test_config)
                writeConfig init_config       -- restore
                
           Nothing -> isJust configMaybe `shouldBe` True

main :: IO ()
main = spec

