-- This file is part of tersmu
-- Copyright (C) 2014 Martin Bays <mbays@sdf.org>
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of version 3 of the GNU General Public License as
-- published by the Free Software Foundation.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see http://www.gnu.org/licenses/.

-- simple irc wrapper for tersmu
-- based on digit's haskell bot
-- http://www.wastedartist.com/scripts/daskeb/daskeb.hs
import Network
import System.IO
import System.IO.Error
import Text.Printf
import Data.List
import System.Exit
import Text.Regex.Posix
import System.Timeout
import Control.Monad.Trans.State
import Control.Monad.IO.Class
import Control.Applicative
import Control.Concurrent (threadDelay)
import Data.Maybe
import Control.Monad

import TersmuIRC

-- import Debug.Trace
-- traceIt x = traceShow x x
 
server = "irc.libera.chat"
port   = 6667
chans   = ["#lojban", "#ckule"]
nick   = "tersmus"
timeoutTime = 200

nicks = [nick, nick++"_"]
 
main = connectToServer >>= listen

connectToServer = do
    h <- connectTo server (PortNumber (fromIntegral port))
    hSetBuffering h NoBuffering
    hSetEncoding h utf8
    password <- readFile "ircPassword"
    write "USER" ((nick++" 0 * :tersmuBot")) h
    write "NICK" (nick++"_") h
    write "PRIVMSG" ("NickServ :regain "++nick++" "++password) h
    write "PRIVMSG" ("NickServ :identify "++nick++" "++password) h

    -- Wait before joining, to give time for the identify to work
    -- TODO: wait until confirmation
    liftIO $ threadDelay $ 5 * 10^6

    forM_ chans $ \chan -> write "JOIN" chan h
    return h
 
write :: String -> String -> Handle -> IO ()
write s t h = do
    hPrintf h "%s %s\r\n" s t
    printf    "> %s %s\n" s t

reconnectingOnError :: (Handle -> IO a) -> StateT Handle IO a
reconnectingOnError m = do
    h <- get
    mret <- liftIO $ (`catchIOError` (const $ return Nothing)) $ timeout (timeoutTime * 10^6) $ m h
    case mret of
	Nothing -> do
	    liftIO $ threadDelay $ 10 * 10^6
	    mh <- liftIO $ (`catchIOError` (const $ return Nothing)) $ Just <$> connectToServer
	    maybe (return ()) put mh
	    reconnectingOnError m
	Just ret -> return ret
 
listen :: Handle -> IO ()
listen h = flip evalStateT h $ forever $ do
    s <- init <$> reconnectingOnError hGetLine
    liftIO $ putStrLn s
    if ping s then pong s else eval s
  where
    forever a = a >> forever a

    clean     = drop 1 . dropWhile (/= ':') . drop 1
 
    ping x    = "PING :" `isPrefixOf` x
    pong x    = reconnectingOnError $ write "PONG" (':' : drop 6 x)

    privmsg :: String -> String -> StateT Handle IO ()
    privmsg to s = reconnectingOnError $ write "PRIVMSG" (to ++ " :" ++ s)

    eval :: String -> StateT Handle IO ()
    eval s = case s =~ ":([^!]+)!([^ ]+) PRIVMSG ([^ ]+) :(<[^>]*>: )*(.*)" of
	[[_,user,_,to,_,msg]] -> let
		isPrivate = to `elem` nicks
		reply = privmsg $ if isPrivate then user else to
		toUs = if isPrivate then msg
		    else fromMaybe "" $ msum [ do
                            guard $ (n++":") `isPrefixOf` msg
                            return $ drop (length $ n++":") $ msg
                        | n <- nicks ]
		(command,args) = case words toUs of
		    [] -> ("",[])
		    (w:ws) -> (filter (/= ':') w,ws)
	    in case command of
		"" -> return ()
		-- "id" -> chanmsg $ unwords args
		"privid" -> reply $ unwords args
		"jbo" -> reply $ onelineParse True $ unwords args
		"loj" -> reply $ onelineParse False $ unwords args
		_ -> reply $ onelineParse False $ unwords (command:args)
	_ -> return ()
