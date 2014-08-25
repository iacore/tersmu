module Main where

import ParseText
import JboParse (evalText, evalStatement)
import JboSyntax
import BridiM (ParseStateT, evalParseStateT, setFrees)
import JboShow
import FOL
import Bindful
import Morphology
import Parse

import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Char
import System.IO
import System.IO.Error
import System.Exit
import System.Process

repl :: IO ()
repl = do 
    putStr "> "
    hFlush stdout
    text <- morph <$> getLine
    --print text
    when (text == "") repl
    evalParseStateT $ mapM showParseResult $ parseText text
    repl

showParseResult :: Either (String,Int) (Statement,[Free]) -> ParseStateT IO ()
showParseResult (Right (s,fs)) = do
    setFrees fs
    ps <- mapStateT (return.runIdentity) $ evalStatement s
    let logstr = evalBindful $ logshow ps
	jbostr = evalBindful $ jboshow ps
	{-
	-- check that jbostr is a fixed point:
	Left checkss = eval jbostr
	True = jbostr == (evalBindful $ jboshow $
		evalText checkss)
	-}
    liftIO $ putStr $
       "\n" ++
       --show s ++ "\n\n"
       --"Prop: " ++
       logstr ++ "\n\n" ++
       --"jbo: " ++
       jbostr ++ "\n\n" ++
       --"PNF: " ++ show (pnf p) ++ "\n\n" ++
       ""
showParseResult (Left (text,pos)) = do
    liftIO $ putStr $ "Parse error:" ++
	"\n\t{" ++ text ++ "}" ++
	"\n\t " ++ replicate pos ' ' ++
	"^" ++
	"\n\n"

main :: IO()
main = repl `catchIOError` (\e -> if isEOFError e then exitWith ExitSuccess
					   else do putStr $ show e
						   exitFailure)

morph :: String -> String
morph s = let Parsed words _ _ = morphologywords $ morphologyParse "words" $ s ++ " "
	in unwords $ words
