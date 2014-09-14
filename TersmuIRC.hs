module TersmuIRC (onelineParse) where

import ParseText (parseText)
import JboParse (evalText, evalStatement)
import JboSyntax
import BridiM (ParseStateM, evalParseStateM, setFrees)
import JboShow
import FOL
import Bindful
import Morphology
import Parse
import Pos

import Control.Monad.State
import Control.Monad.Identity
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import Data.Char
import Data.Either

onelineParse :: Bool -> String -> String
onelineParse jbo s =
    case morph s of
        Left errpos ->
            "Morphology error at " ++ show errpos
        Right text ->
            evalParseStateM $ showParsedText jbo text $ parseText text

showParsedText :: Bool -> String -> Either Int Text -> ParseStateM String
showParsedText jbo s (Right text) = do
    jboText <- mapStateT (return.runIdentity) $ JboParse.evalText text
    return $ onelinify jbo $ evalBindful $ logjboshow jbo jboText
showParsedText jbo s (Left pos) = return $ "Parse error at " ++ show pos

onelinify :: Bool -> String -> String
onelinify jbo "" = ""
onelinify jbo ('\n':cs) = (if jbo then " " else ";  ") ++ onelinify jbo cs
onelinify jbo (c:cs) = c:onelinify jbo cs

stripPunc :: String -> String
stripPunc =
    -- TODO: shouldn't strip inside zoi quotes
    -- (but shouldn't allow "%%%END%%%" in them either...)
    map $ \c -> if isAlphaNum c || isSpace c || c `elem` ",'" then c else ' '

morph :: String -> Either Int String
morph s = let
        Parsed words d _ = morphologywords $ morphologyParse "words" $ stripPunc s ++ " "
        p = posCol (dvPos d) - 1
    in if p < length s
        then Left p
        else Right $ map toLower $ unwords $ words
