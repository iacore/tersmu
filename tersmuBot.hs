-- simple irc wrapper for tersmu
-- based on digit's haskell bot
-- http://www.wastedartist.com/scripts/daskeb/daskeb.hs
import Network
import System.IO
import Text.Printf
import Data.List
import System.Exit

import TersmuIRC
 
server = "irc.freenode.org"
port   = 6667
chan   = "#lojban"
nick   = "tersmus"
 
main = do
    h <- connectTo server (PortNumber (fromIntegral port))
    hSetBuffering h NoBuffering
    write h "NICK" nick
    write h "USER" (nick++" 0 * :digitshaskellbot")
    write h "JOIN" chan
    listen h
 
write :: Handle -> String -> String -> IO ()
write h s t = do
    hPrintf h "%s %s\r\n" s t
    printf    "> %s %s\n" s t
 
listen :: Handle -> IO ()
listen h = forever $ do
    t <- hGetLine h
    let s = init t
    if ping s then pong s else eval $ drop 1 s
    putStrLn s
  where
    forever a = a >> forever a
 
    clean     = drop 1 . dropWhile (/= ':') . drop 1
 
    ping x    = "PING :" `isPrefixOf` x
    pong x    = write h "PONG" (':' : drop 6 x)

    privmsg :: String -> String -> IO ()
    privmsg to s = write h "PRIVMSG" (to ++ " :" ++ s)

    chanmsg = privmsg chan
    
    eval :: String -> IO ()
    eval s = case (elemIndex '!' s, elemIndex ':' s) of
	(Just bn, Just cn) -> let
		u = take bn s
		(h,t) = splitAt cn s
		isMsg = "PRIVMSG" `isInfixOf` h
		to = last $ words h
		x = drop 1 t
		isPrivate = to == nick
		reply = if isPrivate then privmsg u else chanmsg
		toUs = if isPrivate then x
		    else if (nick++":") `isPrefixOf` x
			then drop 1 . dropWhile (/=':') $ x
			else ""
		(command,args) = case words toUs of
		    [] -> ("",[])
		    (w:ws) -> (filter (/= ':') w,ws)
	    in if not isMsg then return () else
	    case command of
		"" -> return ()
		"id" -> chanmsg $ unwords args
		"privid" -> reply $ unwords args
		"jbo" -> reply $ onelineParse True $ unwords args
		"loj" -> reply $ onelineParse False $ unwords args
		_ -> reply $ onelineParse False $ unwords (command:args)
	_ -> return ()
