module Main where

import ParseText
import JboParse (evalText, evalStatement, evalFree)
import JboSyntax
import BridiM (ParseStateT, evalParseStateT)
import JboShow
import FOL
import Bindful

import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import System.IO
import System.IO.Error
import System.Exit
import System.Process

repl :: IO ()
repl = do 
    putStr "> "
    hFlush stdout
    text' <- getLine
    text <- morph text'
    when (text == "") repl
    evalParseStateT $ mapM showParseResult $ parseText (text ++ " ")
    repl

showParseResult :: Either (String,Int) (Statement,[Free]) -> ParseStateT IO ()
showParseResult (Right (s,fs)) = do
    ps <- mapStateT (return.runIdentity) $ do
	fsps <- concat <$> mapM evalFree fs
	stps <- evalStatement s
	return $ fsps ++ stps
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

morph :: String -> IO String
morph = vlatai . (map (\c -> case c of {'.' -> ' '; _ -> c}))

vlatai :: String -> IO String
vlatai s = unwords <$> mapM vlatai' (words s)
    where vlatai' w =
	    do (_, Just out, _, _) <- createProcess
		   (proc "vlatai" [w]){ std_out = CreatePipe } 
	       line <- hGetLine out
	       return $ filter (/='/') $ drop ( (+3) $ last $ findIndices (== ':') line ) line
    -- FIXME: currently dies if we don't have vlatai in the path...
