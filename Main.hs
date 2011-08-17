module Main where

import Tersmu
import FOL

repl :: IO ()
repl = do 
    putStr "> "
    text <- getLine
    let p = eval text in
	putStr $ show p ++ "\n\n" ++ "PNF: " ++ show (pnf p) ++ "\n\n"
    repl

main :: IO()
main = repl 
