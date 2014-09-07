module ParseText (parseText) where

import Tersmu
import Parse
import JboSyntax
import Pos

import Control.Applicative
import Debug.Trace
traceIt x = traceShow x x

parseText :: String -> Either Int ((Text,[Free]),String)
parseText str = traceIt $ stripFrees (tersmuterminatedText . tersmuParse "terminatedText") $ str ++ " %%%END%%%"

-- |parseTextSplitting: split text into statements, strip indicators&free from each,
-- and parse the stripped statements. Unused.
-- Doesn't handle fragments, nor the 'text' production in full detail.
parseTextSplitting :: String -> [ Either (String,Int) (Statement,[Free]) ]
parseTextSplitting = parseText' . stripTextHead . (++" ") where
    parseText' str = case parseStatement str of
	    Left n -> [Left (str,n)]
	    Right (parsed,tail) -> if null tail
		then [Right parsed]
		else Right parsed:parseText' tail
    parseStatement :: String -> Either Int ((Statement,[Free]),String)
    parseStatement = stripFrees $ tersmuwholeStatement . tersmuParse "wholeStatement"
    stripTextHead :: String -> String
    stripTextHead str =
	let Parsed _ d _ = tersmutextHead . tersmuParse "textHead" $ str
	in afterPos (dvPos d) str

afterPos :: Pos -> String -> String
afterPos p s = drop (posCol p - 1) s

-- stripFrees| try to parse; if there's a parse error, and a free can be
-- parsed at the point of the error, strip the free and move it back to the
-- start of the last statement or subsentence or start of text.
-- XXX: this doesn't handle MAI, since the parse error occurs at MAI; we'd
-- need to back up to find the number...
-- More generally, moving our frees like this means that anaphora within them
-- don't resolve correctly.
-- TODO: Would it be enough to move it back to the end of the last sumti or
-- bridi, by allowing free annotations there and inching our annotations back
-- until we get a parse?
-- FIXME: currently we reparse from the head many times while sorting out
-- frees, which is hideously inefficient.
-- FIXME/ARGH: Ugh, no, this approach is fundamentally flawed - consider e.g.
--  to broda bai lo nu ui brode toi
-- where the inner text succeeds parsing up to "bai", and we have no way of
-- telling that it stopped prematurely because of a later free.
-- So we'll need to do some backtracking.
-- Trying to put the free annotation after the last completed term/selbri as
-- mentioned above is, thinking about, even more of a nightmare - since,
-- again, a term might finish parsing prematurely due to further unstripped
-- frees.
-- CONCLUSION: we should DROP this hacky approach, and instead use a proper
-- syntactic parser (camxes) which handles frees in the correct way, and
-- manipulate that parse tree to get it of the form we want.
stripFrees :: (String -> Result TersmuDerivs a)
    -> String -> Either Int ((a,[Free]),String)
stripFrees parse s = fmap (\((a,_,fs),s)->((a,fs),s)) $ stripFrees' False [] [] 0 parse s where
    stripFrees' :: Bool -> [Free] -> [Free] -> Int -> (String -> Result TersmuDerivs a)
	-> String -> Either Int ((a,[Free],[Free]),String)
    stripFrees' inFree unnoted noted countFrom parse str =
	traceShow str $
	let (parsed,pos) = case parse str of
		Parsed a d _ -> (Just a, parsedPoint d)
		NoParse e -> (Nothing, errorPoint e)
	    -- Parsed _ d' _ = parseAnnotations $ drop pos1 str
	    -- pos = pos1 + parsedPoint d'
	in if inFree && pos == 0
	    then Left 0
	    else let (head,tail) = traceIt $ splitAt pos str in
	    case traceIt $ stripFrees' True [] [] (countFrom + length noted) parseFree tail of
		Left 0 -> case parsed of
		    Just a -> Right ((a,unnoted,noted), tail)
		    Nothing -> Left pos
		Left n -> Left $ pos + n
		Right ((newfree,subUnnoted,subNoted),tail') ->
		    let (head',offset,newUnnoted,newNoted) = case traceIt $ addAnnotations inFree head
				$ map (+(countFrom + length subNoted))
				    [0..length subUnnoted] of
			    Just (head'', offset') -> (head'', offset', [], subNoted++subUnnoted++[newfree]) 
			    Nothing -> (head, 0, subUnnoted++[newfree], subNoted)
			unnoted' = unnoted ++ newUnnoted
			noted' = noted ++ newNoted
			countFrom' = countFrom + length newNoted
		    in mapError (+((length tail - length tail')-offset)) $
			stripFrees' inFree unnoted' noted' countFrom' parse $ head'++tail'
    errorPoint e = posCol (errorPos e) - 1
    parsedPoint d = posCol (dvPos d) - 1
    parseAnnotations = tersmufreeAnnotations . tersmuParse "freeAnnotations"
    parseFree = tersmufree . tersmuParse "free"
    mapError :: (e -> e) -> Either e a -> Either e a
    mapError f (Left e) = Left $ f e
    mapError _ (Right x) = Right x
    addAnnotations :: Bool -> String -> [Int] -> Maybe (String,Int)
    addAnnotations inFree s ns =
	let Parsed _ d _ = tersmulastStatementOrSubsentence . tersmuParse "lastStatementOrSubsentence" $ s
	    (head,tail) = splitAt (posCol (dvPos d) - 1) s
	    annotations = concat ["^" ++ show n ++ " " | n <- ns]
	in if inFree && null head then Nothing
	    else Just (head ++ annotations ++ tail, length annotations)

{-
-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case tersmuatext1 (tersmuParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))
-}
