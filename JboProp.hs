module JboProp where

import FOL hiding (Term)
import qualified FOL (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative

type JboProp = Prop JboRel JboTerm

data JboTerm = Var Int
	     | Named String
	     | NonAnaph String
	     | UnboundAssignable Int
	     | UnboundLerfuString [Lerfu]
	     | JboQuote [Statement]
	     | Valsi String
	     | ZoheTerm
	     deriving (Eq, Show, Ord)

data JboRel = ConnectedRels JboConnective JboRel JboRel
	    | PermutedRel Int JboRel
	    | Tanru JboPred JboRel
	    | AbsPred Abstractor JboPred
	    | AbsProp Abstractor JboProp
	    | Moi Quantifier MOICmavo
	    | Among JboTerm
	    | Equal
	    | Brivla String

type JboPred = JboTerm -> JboProp

type Abstractor = String
type MOICmavo = String

instance FOL.Term JboTerm where
    var n = Var n

-- subTerm s t p: replace instances of s with t in p
subTerm :: JboTerm -> JboTerm -> JboProp -> JboProp
subTerm s t = terpProp $ \r -> \ts -> Rel (subTermInRel s t r) $ map (\x -> if x==s then t else x) ts
subTermInRel t t' (Tanru p r) = Tanru (\o -> subTerm t t' (p o)) (subTermInRel t t' r)
subTermInRel t t' (AbsPred a p) = AbsPred a (\o -> subTerm t t' (p o))
subTermInRel t t' (AbsProp a p) = AbsProp a (subTerm t t' p)
subTermInRel _ _ r = r

connToFOL :: JboConnective -> JboProp -> JboProp -> JboProp
connToFOL (JboConnective True 'e' True) p1 p2 = Connected And p1 p2
connToFOL (JboConnective True 'a' True) p1 p2 = Connected Or p1 p2
connToFOL (JboConnective False 'a' True) p1 p2 = Connected Impl p1 p2
connToFOL (JboConnective True 'a' False) p1 p2 = Connected Impl p2 p1
connToFOL (JboConnective True 'o' True) p1 p2 = Connected Equiv p1 p2
connToFOL (JboConnective True 'u' True) p1 p2 = p1
connToFOL (JboConnective True 'U' True) p1 p2 = p2
connToFOL (JboConnective False c b2) p1 p2 =
    connToFOL (JboConnective True c b2) (Not p1) p2
connToFOL (JboConnective b1 c False) p1 p2 =
    connToFOL (JboConnective b1 c True) p1 (Not p2)
