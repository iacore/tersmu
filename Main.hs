module Main where

import Tersmu
import JboParse (parseStatements)
import BridiM (runJboPropM)
import JboShow
import FOL
import Bindful

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import System.IO
import System.IO.Error
import System.Exit
import System.Process

repl :: IO ()
repl = do 
    text' <- getLine
    text <- morph text'
    when (text == "") repl
    case eval text of
	 Left ss ->
	     let p = runJboPropM $ parseStatements ss
		 logstr = evalBindful $ logshow p
		 jbostr = evalBindful $ jboshow p
		 -- check that jbostr is a fixed point:
		 Left checkss = eval jbostr
		 True = jbostr == (evalBindful $ jboshow $
			 runJboPropM $ parseStatements checkss)
	     in putStr $ 
		--show s ++ "\n\n"
		"Prop: " ++ logstr ++ "\n" ++
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
main = repl `catchIOError` (\e -> if isEOFError e then exitWith ExitSuccess
					   else do putStr $ show e
						   exitFailure)

morph :: String -> IO String
morph = vlatai . (map (\c -> case c of {'.' -> ' '; _ -> c}))

vlatai :: String -> IO String
vlatai s = do vws <- sequence $ map vlatai' (words s)
	      return $ unwords vws
    where vlatai' w =
	    do (_, Just out, _, _) <- createProcess
		   (proc "vlatai" [w]){ std_out = CreatePipe } 
	       line <- hGetLine out
	       return $ drop ( (+3) $ last $ findIndices (== ':') line ) line
    -- FIXME: currently dies if we don't have vlatai in the path...
