module ParseText (parseText) where

import Tersmu
import Parse
import JboSyntax
import Pos

import Control.Applicative

-- |parseText: split text into statements, strip indicators&free from each,
-- and parse the stripped statements.
-- TODO: fragments, and handling the 'text' production in full detail
-- (Note: could just use the 'text' production, but then a failure in one
-- statement causes the whole text to fail) 
parseText :: String -> [ Either (String,Int) (Statement,[Free]) ]
parseText = parseText' . stripTextHead . (++" ")
    where parseText' str = case parseStatement str of
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

-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case tersmuatext1 (tersmuParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))
