module ParseText (parseText) where

import Tersmu
import Parse
import JboSyntax
import Pos

import Control.Applicative

-- |parseText: split text into statements, strip indicators&free from each,
-- and parse the stripped statements.
-- TODO: fragments, and handling the 'text' production in full detail
-- XXX: the same treatment is *not* given to the nested paragraphs of a
--  TO ... [TOI] production; instead, all subfrees are lifted to the same
--  level as that free.
--  Similarly, frees in subsentences (e.g. in abstractions) are associated
--  with the enclosing top level statement rather than the subsentence.
--  Same with quotes.
--  These are all problematic.
--  See notes/free for a solution.
parseText :: String -> [ Either (String,Int) (Statement,[Free]) ]
parseText = parseText' . stripTextHead 
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
afterPos d s = drop (posCol d - 1) s

stripFrees :: (String -> Result TersmuDerivs a)
    -> String -> Either Int ((a,[Free]),String)
stripFrees = stripFrees' False [] where
    stripFrees' :: Bool -> [Free] -> (String -> Result TersmuDerivs a)
	-> String -> Either Int ((a,[Free]),String)
    stripFrees' inFree frees parse str = case parse str of
	Parsed a d _ -> Right ((a,frees), afterPos (dvPos d) str)
	NoParse e ->
	    let ep = errorPoint e
	    in if inFree && ep == 0
	    then Left 0
	    else let (head,tail) = splitAt ep str in
	    case stripFrees' True [] (tersmufrees . tersmuParse "frees") tail of
		Left n -> Left $ ep + n
		Right ((frees',frees''),tail') ->
		    stripFrees' inFree (frees++frees'++frees'') parse $ head++tail'
    errorPoint :: ParseError -> Int
    errorPoint e = posCol (errorPos e) - 1

-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case tersmuatext1 (tersmuParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))
