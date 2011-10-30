module Main where

import Tersmu
import Lojban
import FOL
import Bindful

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import IO
import System.Exit

repl :: IO ()
repl = do 
    text <- getLine
    when (text == "") repl
    case eval text of
	 Left ss ->
	     let p = statementsToProp ss Map.empty
		 logstr = evalBindful $ logshow p
		 jbostr = evalBindful $ jboshow p
		 -- check that jbostr is a fixed point:
		 Left checkss = eval jbostr
		 True = jbostr == (evalBindful $ jboshow $
			 statementsToProp checkss Map.empty)
	     in putStr $ 
		--show s ++ "\n\n"
		"Prop:" ++ logstr ++ "\n\n" ++
		"jbo: " ++ jbostr ++ "\n\n" ++
		--"PNF: " ++ show (pnf p) ++ "\n\n" ++
		""
	 Right pos ->
	     putStr $ "Parse error:" ++
		  "\n\t{" ++ text ++ "}" ++
		      "\n\t" ++ replicate pos ' ' ++
		      "^" ++
		      "\n\n"
    repl

main :: IO()
main = repl `catch` (\e -> if isEOFError e then exitWith ExitSuccess
					   else do putStr $ show e
						   exitFailure)
