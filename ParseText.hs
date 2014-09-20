module ParseText (parseText) where

import Tersmu
import Pappy.Pos
import Pappy.Parse
import JboSyntax

import Control.Applicative
-- import Debug.Trace
-- traceIt x = traceShow x x

parseText :: String -> Either Int Text
parseText str = nudgeFrees (tersmuterminatedText . tersmuParse "terminatedText") $ str ++ " %%%END%%%"

afterPos :: Pos -> String -> String
afterPos p s = drop (posCol p - 1) s

-- |nudgeFrees: move indicators and frees backwards until they're in one of
-- the prescribed positions where our main grammar can parse them (basically:
-- after a term, or at the start of a sentence or similar construct).
-- Works as follows: try to parse; if fail, try to parse a free at fail point,
-- recursively nudging frees to do so; if find such a misplaced free, move it
-- back a word and try parsing again.
-- Rather a hack, obviously, but it seems to work!
--
-- FIXME: MAI isn't really handled, since the parse failure can come at the
-- MAI rather than the start of the free, so e.g. "za'u re'u re mai broda"
-- fails. Similarly {le zarci e re mai le zdani}
--
-- FIXME: {li ci xi pa su'i vo} - nudging the xi clause back has it pick up
-- the {ci}, resulting in a parse error...
--
-- XXX: possible source of parse bugs: misplaced free can interrupt crucial
-- greed. e.g. "tag sumti / tag KU?" acts buggily on "vi ue ta",
-- and has to be "tag sumti / tag !free KU". I think I've got all those now,
-- but may be wrong.
--
-- TODO: optimise; currently we're doing string manipulation with String,
-- which is a bad idea, and more to the point we're reparsing the whole text
-- repeatedly. Chunking the text into paragraphs would be a start.
--
nudgeFrees :: (String -> Result TersmuDerivs a) -> String -> Either Int a
nudgeFrees parse s = fmap fst $ nudgeFrees' False parse s where
    nudgeFrees' :: Bool -> (String -> Result TersmuDerivs a) -> String -> Either Int (a,Int)
    nudgeFrees' inFree parse str =
	case parse str of
	    Parsed a d _ -> Right (a, parsedPoint d)
	    NoParse e ->
		let pos = errorPoint e
		    (head,tail) = splitAt pos str
		in if inFree && pos == 0 then Left 0
		else case nudgeFrees' True parseFree tail of
		    Left n -> Left $ pos + n
		    Right (_,flen) ->
			nudgeFrees' inFree parse $ nudgeFree head tail flen
    errorPoint e = posCol (errorPos e) - 1
    parsedPoint d = posCol (dvPos d) - 1
    parseFree = tersmufree . tersmuParse "free"
    nudgeFree head tail flen =
	let ws = words head
	    (headws',headws'') = splitAt (length ws - 1) ws
	    (free,tail') = splitAt flen tail
	in unwords headws' ++ (if null headws' then "" else " ") ++
	    free ++ unwords headws'' ++ " " ++ tail'

{-
-- Direct parsing without any preprocessing - currently unused
parseAText :: String -> Either Int [Statement]
parseAText str = case tersmuatext1 (tersmuParse "atext1" (str ++ " ")) of
	Parsed p _ _ -> Right p
	NoParse e -> Left (posCol (errorPos e))

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
-}
