-- simple irc wrapper for tersmu
-- based on digit's haskell bot
-- http://www.wastedartist.com/scripts/daskeb/daskeb.hs
import Network
import System.IO
import Text.Printf
import Data.List
import System.Exit
import Text.Regex.Posix

import TersmuIRC

-- import Debug.Trace
-- traceIt x = traceShow x x
 
server = "morgan.freenode.net"
--server = "irc.freenode.org"
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
    putStrLn s
    if ping s then pong s else eval s
  where
    forever a = a >> forever a
 
    clean     = drop 1 . dropWhile (/= ':') . drop 1
 
    ping x    = "PING :" `isPrefixOf` x
    pong x    = write h "PONG" (':' : drop 6 x)

    privmsg :: String -> String -> IO ()
    privmsg to s = write h "PRIVMSG" (to ++ " :" ++ s)

    chanmsg = privmsg chan
    
    eval :: String -> IO ()
    eval s = case s =~ ":([^!]+)!([^ ]+) PRIVMSG ([^ ]+) :(.*)" of
	[[_,user,_,to,msg]] -> let
		isPrivate = to == nick
		reply = if isPrivate then privmsg user else chanmsg
		toUs = if isPrivate then msg
		    else if (nick++":") `isPrefixOf` msg
			then drop (length $ nick++":") $ msg
			else ""
		(command,args) = case words toUs of
		    [] -> ("",[])
		    (w:ws) -> (filter (/= ':') w,ws)
	    in case command of
		"" -> return ()
		"id" -> chanmsg $ unwords args
		"privid" -> reply $ unwords args
		"jbo" -> reply $ onelineParse True $ unwords args
		"loj" -> reply $ onelineParse False $ unwords args
		_ -> reply $ onelineParse False $ unwords (command:args)
	_ -> return ()
