module JboProp where

import FOL hiding (Term)
import qualified FOL (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative
import Data.Foldable (traverse_, Foldable)
import Control.Monad.Writer

type JboProp = Prop JboRel JboTerm Joik JboModalOp JboQuantifier

data JboTerm = BoundVar Int
	     | Var Int
	     | Constant Int [JboTerm]
	     | Named String
	     | NonAnaph String
	     | UnboundSumbasti SumtiAtom
	     | JboQuote ParsedQuote
	     | JboErrorQuote [String]
	     | JboNonJboQuote String
	     | TheMex Mex -- me'o
	     | Value JboMex -- li
	     | Valsi String
	     | ZoheTerm
	     | JoikedTerms Joik JboTerm JboTerm
	     | QualifiedTerm SumtiQualifier JboTerm
	     deriving (Eq, Show, Ord)

data JboRel = Tanru JboPred JboRel
	    | TanruConnective JboConnective JboPred JboPred
	    | ScalarNegatedRel NAhE JboRel
	    | AbsPred Abstractor JboPred
	    | AbsProp Abstractor JboProp
	    | Moi JboMex Cmavo
	    | Among JboTerm
	    | Equal
	    | UnboundBribasti TanruUnit
	    | TagRel JboTag -- xo'i
	    | Brivla String
    deriving (Eq, Show, Ord)

data JboModalOp
    = JboTagged JboTag (Maybe JboTerm)
    | QTruthModal
    | WithEventAs JboTerm
type JboTag = AbsTag JboPred JboTerm
type JboDecoratedTagUnit = DecoratedAbsTagUnit JboPred JboTerm
type JboTagUnit = AbsTagUnit JboPred JboTerm
type JboConnective = AbsConnective JboPred JboTerm

type JboPred = JboTerm -> JboProp

type JboMex = AbsMex JboPred JboTerm
type JboOperator = AbsOperator JboPred JboTerm

data JboQuantifier
    = MexQuantifier JboMex
    | LojQuantifier LojQuantifier
    | QuestionQuantifier
    deriving (Eq, Show, Ord)

instance FOL.Term JboTerm where
    var n = BoundVar n

-- |ParsedQuote: using this newtype so we can provide dummy instances for use
-- in derived instances for JboTerm
newtype ParsedQuote = ParsedQuote [JboProp]
instance Eq ParsedQuote where x == y = False
instance Show ParsedQuote where show q = "<< ... >>"
instance Ord ParsedQuote where x <= y = False

-- can't derive instances for props, since we handle quantifiers with
-- functions, so we define these dummy ones to allow derivations for other
-- types
instance Eq JboProp where { _ == _ = False }
instance Show JboProp where { show _ = "[ ... ]" }
instance Ord JboProp where { _ <= _ = False }
instance Eq JboPred where { _ == _ = False }
instance Show JboPred where { show _ = "[ \\_ -> ... ]" }
instance Ord JboPred where { _ <= _ = False }

-- subTerm s t p: replace instances of s with t in p
subTerm :: JboTerm -> JboTerm -> JboProp -> JboProp
subTerm s t = terpProp
    (\r -> \ts -> Rel (subTermInRel r) $ map subTermInTerm ts)
    subTermInOp
    subTermInMex
    where
    subTermInTerm (JoikedTerms joik t1 t2) = JoikedTerms joik (subTermInTerm t1) (subTermInTerm t2)
    subTermInTerm (QualifiedTerm qual t) = QualifiedTerm qual (subTermInTerm t)
    subTermInTerm (Constant n ts) = Constant n $ map subTermInTerm ts
    subTermInTerm x = if x == s then t else x
    subTermInRel (Tanru p r) = Tanru (subTermInPred p) (subTermInRel r)
    subTermInRel (TanruConnective con p p') = TanruConnective (subTermInCon con) (subTermInPred p) (subTermInPred p')
    subTermInRel (AbsPred a p) = AbsPred a (\o -> subTerm s t (p o))
    subTermInRel (AbsProp a p) = AbsProp a (subTerm s t p)
    subTermInRel (Among t) = Among $ subTermInTerm t
    subTermInRel r = r
    subTermInOp (JboTagged tag mt) =
	JboTagged (subTermInTag tag) $ if mt == Just s then Just t else mt
    subTermInOp (WithEventAs x) = WithEventAs $ subTermInTerm x
    subTermInOp op = op
    subTermInTag (ConnectedTag con tag1 tag2) =
	ConnectedTag (subTermInCon con) (subTermInTag tag1) (subTermInTag tag2)
    subTermInTag (DecoratedTagUnits dtus) = DecoratedTagUnits $ map subTermInDTU dtus
    subTermInDTU (DecoratedTagUnit nahe se nai tu) = DecoratedTagUnit nahe se nai $ subTermInTagUnit tu
    subTermInTagUnit (FIhO fiho) = FIhO $ subTermInPred fiho
    subTermInTagUnit tu = tu
    subTermInCon (JboConnLog (Just tag) lcon) = JboConnLog (Just $ subTermInTag tag) lcon
    subTermInCon (JboConnJoik (Just tag) joik) = JboConnJoik (Just $ subTermInTag tag) joik
    subTermInCon c = c
    subTermInPred p = \x -> subTerm s t (p x)
    subTermInMex = id -- TODO

-- TODO: would be neater to make a proper Traversable instance, such that
-- subTerm above could use it too - but I'm not sure how to handle quantifiers
class Termful t where
    --traverseTerms :: Applicative f => (JboTerm -> f JboTerm) -> t -> f t
    traverseTerms_,travTs_ :: Applicative f => (JboTerm -> f ()) -> t -> f ()
    travTs_ = traverseTerms_
    traverseTerms_ = travTs_

    travtravTs_ :: (Termful t, Applicative f, Foldable fo) =>
	(JboTerm -> f()) -> fo t -> f ()
    travtravTs_ = traverse_ . traverseTerms_ 
    --traverseTerms_ f = (\x -> ()) <$> traverseTerms (\t -> f t *> pure (Var 0))
instance (Termful r, Termful c, Termful o, Termful q) => Termful (Prop r JboTerm c o q) where
    travTs_ f (Rel r ts) = travTs_ f r *> traverse_ f ts
    travTs_ f (Quantified q r p) =
	travTs_ f q *>
	case r of {Nothing -> pure (); Just r' -> travTs_ f (r' 0)}
	*> travTs_ f (p 0)
    travTs_ f (Not p) = travTs_ f p
    travTs_ f (Connected con p1 p2) = travTs_ f con *> travtravTs_ f [p1,p2]
    travTs_ f (NonLogConnected con p1 p2) = travTs_ f con *> travtravTs_ f [p1,p2]
    travTs_ f Eet = pure ()
    travTs_ f (Modal o p) = travTs_ f o *> travTs_ f p
instance Termful FOL.Connective where travTs_ _ _ = pure ()
instance Termful Joik where travTs_ _ _ = pure ()
instance Termful JboQuantifier where
    travTs_ f (LojQuantifier q) = travTs_ f q
    travTs_ f (MexQuantifier m) = travTs_ f m
    travTs_ _ _ = pure ()
instance Termful LojQuantifier where travTs_ _ _ = pure ()
instance Termful JboRel where
    travTs_ f (Tanru p r) = travTs_ f p *> travTs_ f r
    travTs_ f (TanruConnective con p1 p2) = travTs_ f con *> travtravTs_ f [p1,p2]
    travTs_ f (AbsPred a p) = travTs_ f p
    travTs_ f (AbsProp a p) = travTs_ f p
    travTs_ f (Among t) = f t
    travTs_ _ _ = pure ()
instance Termful JboPred where travTs_ f p = travTs_ f $ p ZoheTerm
instance Termful JboModalOp where
    travTs_ f (JboTagged tag mt) = travTs_ f tag *> traverse_ f mt
    travTs_ f (WithEventAs x) = f x
instance Termful JboTag where
    travTs_ f (ConnectedTag con tag1 tag2) = travTs_ f con *> travtravTs_ f [tag1,tag2]
    travTs_ f (DecoratedTagUnits dtus) = travtravTs_ f dtus
instance Termful JboDecoratedTagUnit where travTs_ f (DecoratedTagUnit nahe se nai tu) = travTs_ f tu
instance Termful JboTagUnit where
    travTs_ f (FIhO fiho) = travTs_ f fiho
    travTs_ _ _ = pure ()
instance Termful JboConnective where
    travTs_ f (JboConnLog (Just tag) _) = travTs_ f tag
    travTs_ f (JboConnJoik (Just tag) _) = travTs_ f tag
    travTs_ _ _ = pure ()
instance Termful JboMex where
    travTs_ f (Operation op ms) = travTs_ f op *> travtravTs_ f ms
    travTs_ f (ConnectedMex _ con m1 m2) = travTs_ f con *> travtravTs_ f [m1,m2]
    travTs_ f (QualifiedMex _ m) = travTs_ f m
    travTs_ f (MexSelbri r) = travTs_ f r
    travTs_ f (MexSumti t) = f t
    travTs_ f (MexArray ms) = travtravTs_ f ms
    travTs_ _ _ = pure ()
instance Termful JboOperator where
    travTs_ f (ConnectedOperator _ con op1 op2) = travTs_ f con *> travtravTs_ f [op1,op2]
    travTs_ f (OpPermuted _ op) = travTs_ f op
    travTs_ f (OpScalarNegated _ op) = travTs_ f op
    travTs_ f (OpMex m) = travTs_ f m
    travTs_ f (OpSelbri r) = travTs_ f r
    travTs_ _ _ = pure ()


freeVars :: JboProp -> [JboTerm]
freeVars p = execWriter $ collectFrees p where
	collectFrees = traverseTerms_ collectFreesInTerm
	collectFreesInTerm free@(Var _) = tell $ [free]
	collectFreesInTerm free@(UnboundSumbasti (MainBridiSumbasti _)) = tell $ [free]
	collectFreesInTerm (JoikedTerms joik t1 t2) = collectFreesInTerm t1 *> collectFreesInTerm t2
	collectFreesInTerm (QualifiedTerm qual t) = collectFreesInTerm t
	collectFreesInTerm (Constant _ ts) = traverse_ collectFreesInTerm ts
	collectFreesInTerm _ = pure ()

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
