module JboProp where

import FOL hiding (Term)
import qualified FOL (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative

type JboProp = Prop JboRel JboTerm Joik JboOperator

data JboTerm = Var Int
	     | PreVar Int
	     | Constant Int
	     | Named String
	     | NonAnaph String
	     | UnboundAssignable Int
	     | UnboundLerfuString [Lerfu]
	     | JboQuote ParsedQuote
	     | JboErrorQuote [String]
	     | JboNonJboQuote String
	     | Valsi String
	     | ZoheTerm
	     | JoikedTerms Joik JboTerm JboTerm
	     deriving (Eq, Show, Ord)

data JboRel = Tanru JboPred JboRel
	    | TanruConnective JboConnective JboPred JboPred
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
type JboConnective = AbsConnective JboTag

type JboPred = JboTerm -> JboProp

type Abstractor = String

instance FOL.Term JboTerm where
    var n = Var n

-- |ParsedQuote: using this newtype so we can provide dummy instances for use
-- in derived instances for JboTerm
newtype ParsedQuote = ParsedQuote [JboProp]
instance Eq ParsedQuote where x == y = False
instance Show ParsedQuote where show q = "<< ... >>"
instance Ord ParsedQuote where x <= y = False

-- subTerm s t p: replace instances of s with t in p
subTerm :: JboTerm -> JboTerm -> JboProp -> JboProp
subTerm s t = terpProp
    (\r -> \ts -> Rel (subTermInRel r) $ map subTermInTerm ts)
    subTermInOp
    where
    subTermInTerm (JoikedTerms joik t1 t2) = JoikedTerms joik (subTermInTerm t1) (subTermInTerm t2)
    subTermInTerm x = if x == s then t else x
    subTermInRel (Tanru p r) = Tanru (subTermInPred p) (subTermInRel r)
    subTermInRel (TanruConnective con p p') = TanruConnective con (subTermInPred p) (subTermInPred p')
    subTermInRel (AbsPred a p) = AbsPred a (\o -> subTerm s t (p o))
    subTermInRel (AbsProp a p) = AbsProp a (subTerm s t p)
    subTermInRel r = r
    subTermInOp (JboTagged tag mt) =
	JboTagged (subTermInTag tag) $ if mt == Just s then Just t else mt
    subTermInOp (WithEventAs x) = WithEventAs $ subTermInTerm x
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

joikToFOL :: Joik -> JboProp -> JboProp -> JboProp
joikToFOL joik = NonLogConnected joik

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]

andMPred :: [JboPred] -> Maybe JboPred
andMPred [] = Nothing
andMPred ps = Just $ andPred ps

isAmong :: JboTerm -> (JboTerm -> JboProp)
isAmong y = \o -> Rel (Among y) [o]
