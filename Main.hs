module Main where

import Tersmu
import Lojban
import FOL
import Bindful

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

repl :: IO ()
repl = do 
    putStr "> "
    text <- getLine
    case eval text of
	 Left ss ->
	     let p = statementsToProp ss Map.empty
	     in putStr $ 
		--show s ++ "\n\n"
		"Prop:" ++ (evalBindful $ logshow p) ++ "\n\n" ++
		"jbo: " ++ (evalBindful $ jboshow p) ++ "\n\n" ++
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
main = repl 
