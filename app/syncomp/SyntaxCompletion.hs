module SyntaxCompletion (computeCand) where

import CommonParserUtil 

import Expr

import TokenInterface
import Terminal
import Lexer (lexerSpec)
-- import Parser (parserSpec)
import qualified ParserBidiLinks as PBLinks
import System.IO

-- for syntax completion
import Token
import SynCompInterface
import Control.Exception
import Data.Typeable

-- Todo: The following part should be moved to the library.
--       Arguments: lexerSpec, parserSpec
--                  isSimpleMode
--                  programTextUptoCursor, programTextAfterCursor

maxLevel = 10000

-- | computeCand
computeCand :: Bool -> String -> String -> Bool -> IO [EmacsDataItem]
computeCand debug programTextUptoCursor programTextAfterCursor isSimpleMode = (do
  {- 1. Parsing -}
  ((do ast <- parsing debug PBLinks.parserSpec ((),1,1,programTextUptoCursor)
       successfullyParsed)

    `catch` \parseError ->
      case parseError :: ParseError Token AST () of
        _ ->
          {- 3. Lexing the rest and computing candidates with it -}
          do handleParseError
               (defaultHandleParseError {
                   debugFlag=debug,
                   searchMaxLevel=maxLevel,
                   simpleOrNested=isSimpleMode,
                   postTerminalList=[], --terminalListAfterCursor is set to []!
                   nonterminalToStringMaybe=Nothing})
               parseError))

  `catch` \lexError ->  case lexError :: LexError of  _ -> handleLexError
