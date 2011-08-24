module Main where

import Tersmu
import Lojban
import FOL

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

repl :: IO ()
repl = do 
    putStr "> "
    text <- getLine
    let s = eval text
	p = sentToProp s emptyPropCxt
	in
	putStr $ show s ++ "\n\nProp:" ++ show p ++ "\n\nPNF: " ++ show (pnf p) ++ "\n\n"
    repl

main :: IO()
main = repl 
