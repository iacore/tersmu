module Main where

import ParseText (parseText)
import JboParse (evalText, evalStatement)
import JboSyntax
import BridiM (ParseStateT, evalParseStateT, setFrees)
import JboShow
import FOL
import Bindful
import Morphology
import Parse
import Pos

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
    putStr "> "
    hFlush stdout
    s <- getLine
    case morph s of
        Left errpos ->
            highlightError errpos s "Morphology error"
        Right text ->
            evalParseStateT $ showParsedText text $ parseText text
    repl

showParsedText :: String -> Either Int ((Text,[Free]),String) -> ParseStateT IO ()
showParsedText s (Right ((text,fs),leftover)) = do
    setFrees fs
    jboText <- mapStateT (return.runIdentity) $ JboParse.evalText text
    when (not $ null jboText) $ do
        let logstr = evalBindful $ logshow jboText
            jbostr = evalBindful $ jboshow jboText
        liftIO $ putStr $ "\n" ++ logstr ++ "\n\n" ++ jbostr ++ "\n\n"
    when (not $ null leftover) $
        liftIO $ putStrLn $ "Unparsed: "++leftover
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

stripPunc :: String -> String
stripPunc =
    -- TODO: shouldn't strip inside zoi quotes
    -- (but shouldn't allow "%%%END%%%" in them either...)
    map $ \c -> if isAlphaNum c || isSpace c || c `elem` ",'" then c else ' '

morph :: String -> Either Int String
morph s = let
        Parsed words d _ = morphologywords $ morphologyParse "words" $ stripPunc s ++ " "
        p = posCol (dvPos d) - 1
    in if p < length s
        then Left p
        else Right $ map toLower $ unwords $ words
