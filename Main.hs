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
    let s = eval text
	p = statementToProp s Map.empty
	in
	putStr $ 
	    --show s ++ "\n\n"
	    "Prop:" ++ (evalBindful $ logshow p) ++ "\n\n" ++
	    "jbo: " ++ (evalBindful $ jboshow p) ++ "\n\n" ++
	    --"PNF: " ++ show (pnf p) ++ "\n\n" ++
	    ""
    repl

main :: IO()
main = repl 
