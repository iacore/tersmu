module JboProp where

import FOL hiding (Term)
import qualified FOL (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative

type JboProp = Prop JboRel JboTerm JboOperator

data JboTerm = Var Int
	     | Constant Int
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
	    | Moi Quantifier Cmavo
	    | Among JboTerm
	    | Equal
	    | Brivla String

data JboOperator
    = JboTagged JboTag (Maybe JboTerm)
    | WithEventAs JboTerm
type JboTag = AbsTag Quantifier JboPred
type JboTagUnit = AbsTagUnit Quantifier JboPred

type JboPred = JboTerm -> JboProp

type Abstractor = String

instance FOL.Term JboTerm where
    var n = Var n

-- subTerm s t p: replace instances of s with t in p
subTerm :: JboTerm -> JboTerm -> JboProp -> JboProp
subTerm s t = terpProp
    (\r -> \ts -> Rel (subTermInRel r) $ map (\x -> if x==s then t else x) ts)
    subTermInOp
    where
    subTermInRel (Tanru p r) = Tanru (\o -> subTerm s t (p o)) (subTermInRel r)
    subTermInRel (AbsPred a p) = AbsPred a (\o -> subTerm s t (p o))
    subTermInRel (AbsProp a p) = AbsProp a (subTerm s t p)
    subTermInRel r = r
    subTermInOp (JboTagged tag mt) =
	JboTagged (subTermInTag tag) $ if mt == Just s then Just t else mt
    subTermInOp (WithEventAs x) = WithEventAs $ if x==s then t else x
    subTermInTag (ConnectedTag conn tag1 tag2) =
	ConnectedTag conn (subTermInTag tag1) (subTermInTag tag2)
    subTermInTag (DecoratedTagUnits dtus) = DecoratedTagUnits $ map subTermInDTU dtus
    subTermInDTU (DecoratedTagUnit nahe se nai tu) = DecoratedTagUnit nahe se nai $ subTermInTagUnit tu
    subTermInTagUnit (FIhO fiho) = FIhO $ subTermInPred fiho
    subTermInTagUnit tu = tu
    subTermInPred p = \x -> subTerm s t (p x)

connToFOL :: LogJboConnective -> JboProp -> JboProp -> JboProp
connToFOL (LogJboConnective True 'e' True) p1 p2 = Connected And p1 p2
connToFOL (LogJboConnective True 'a' True) p1 p2 = Connected Or p1 p2
connToFOL (LogJboConnective False 'a' True) p1 p2 = Connected Impl p1 p2
connToFOL (LogJboConnective True 'a' False) p1 p2 = Connected Impl p2 p1
connToFOL (LogJboConnective True 'o' True) p1 p2 = Connected Equiv p1 p2
connToFOL (LogJboConnective True 'u' True) p1 p2 = p1
connToFOL (LogJboConnective True 'U' True) p1 p2 = p2
connToFOL (LogJboConnective False c b2) p1 p2 =
    connToFOL (LogJboConnective True c b2) (Not p1) p2
connToFOL (LogJboConnective b1 c False) p1 p2 =
    connToFOL (LogJboConnective b1 c True) p1 (Not p2)

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]

andMPred :: [JboPred] -> Maybe JboPred
andMPred [] = Nothing
andMPred ps = Just $ andPred ps

isAmong :: JboTerm -> (JboTerm -> JboProp)
isAmong y = \o -> Rel (Among y) [o]
