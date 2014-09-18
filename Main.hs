module Main where

import ParseText (parseText)
import JboParse (evalText, evalStatement)
import JboSyntax
import BridiM (ParseStateT, evalParseStateT)
import JboShow
import FOL
import Bindful
import Morph

import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Char
import Data.Either
import System.IO
import System.IO.Error
import System.Exit
import System.Process

repl :: IO ()
repl = do 
    -- putStr "> "
    -- hFlush stdout
    s <- getLine
    case morph s of
        Left errpos ->
            highlightError errpos s "Morphology error"
        Right text ->
            evalParseStateT $ showParsedText text $ parseText text
    repl

showParsedText :: String -> Either Int Text -> ParseStateT IO ()
showParsedText s (Right text) = do
    jboText <- mapStateT (return.runIdentity) $ JboParse.evalText text
    when (not $ null jboText) $ do
        let logstr = evalBindful $ logshow jboText
            jbostr = evalBindful $ jboshow jboText
        liftIO $ putStr $ "\n" ++ logstr ++ "\n\n" ++ jbostr ++ "\n\n"
showParsedText s (Left pos) = highlightError pos s "Parse error"

highlightError pos s errstr = let context = 40 in
    liftIO $ putStr $ errstr++":" ++
	"\n\t{" ++ take (context*2) (drop (pos-context) s) ++ "}" ++
	"\n\t " ++ replicate (min pos context) ' ' ++
	"^" ++
	"\n\n"

main :: IO ()
main = repl `catchIOError` (\e -> if isEOFError e then exitWith ExitSuccess
					   else do putStr $ show e
						   exitFailure)
