module Morph (morph) where
import Morphology
import Data.Char
import Parse
import Pos

morph :: String -> Either Int String
morph s = let
        Parsed words d _ = morphologywords $ morphologyParse "words" $ stripPunc s ++ " "
        p = posCol (dvPos d) - 1
    in if p < length s
        then Left p
        else Right $ map toLower $ unwords $ words

stripPunc :: String -> String
stripPunc =
    -- TODO: shouldn't strip inside zoi quotes
    -- (but shouldn't allow "%%%END%%%" in them either...)
    map $ \c -> if isAlphaNum c || isSpace c || c `elem` ",'" then c else ' '
