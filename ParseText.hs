module ParseText (parseText) where

import Tersmu
import Parse
import JboSyntax
import Pos

import Control.Applicative

parseText :: String -> Either Int ((Text,[Free]),String)
parseText str = stripFrees (tersmuterminatedText . tersmuParse "terminatedText") $ str ++ " %%%END%%%"

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
-- TODO: Would it be enough to move it back to the end of the last sumti, by
-- allowing free annotations there and inching our annotations back until we
-- get a parse?
-- FIXME: I seem to have broken frees within frees, not sure how or when...
stripFrees :: (String -> Result TersmuDerivs a)
    -> String -> Either Int ((a,[Free]),String)
stripFrees = stripFrees' False [] 0 where
    stripFrees' :: Bool -> [Free] -> Int -> (String -> Result TersmuDerivs a)
	-> String -> Either Int ((a,[Free]),String)
    stripFrees' inFree frees countFrom parse str = case parse str of
	Parsed a d _ -> Right ((a,frees), afterPos (dvPos d) str)
	NoParse e ->
	    let ep = errorPoint e
	    in if inFree && ep == 0
	    then Left 0
	    else let (head,tail) = splitAt ep str in
	    case stripFrees' True [] (countFrom + length frees) (tersmufrees . tersmuParse "frees") tail of
		Left n -> Left $ ep + n
		Right ((newfrees,subfrees),tail') ->
		    let (head',offset) = addAnnotations head
			    $ map (+(countFrom + length subfrees))
				[0..length newfrees - 1]
		    in mapError (+((length tail - length tail')-offset)) $ stripFrees' inFree
			(frees++subfrees++newfrees)
			(countFrom + length subfrees + length newfrees)
			parse $ head'++tail'
    errorPoint :: ParseError -> Int
    errorPoint e = posCol (errorPos e) - 1
    mapError :: (e -> e) -> Either e a -> Either e a
    mapError f (Left e) = Left $ f e
    mapError _ (Right x) = Right x
    addAnnotations :: String -> [Int] -> (String,Int)
    addAnnotations s ns =
	let Parsed _ d _ = tersmulastStatementOrSubsentence . tersmuParse "lastStatementOrSubsentence" $ s
	    (head,tail) = splitAt (posCol (dvPos d) - 1) s
	    annotations = concat ["^" ++ show n ++ " " | n <- ns]
	in (head ++ annotations ++ tail, length annotations)

{-
-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case tersmuatext1 (tersmuParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))
-}
