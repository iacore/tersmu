module JboProp where

import FOL hiding (Term)
import qualified FOL (Term)
import JboSyntax

import Bindful

import Data.Maybe
import Control.Applicative
import Data.Foldable (traverse_)
import Control.Monad.Writer

type JboProp = Prop JboRel JboTerm Joik JboOperator

data JboTerm = BoundVar Int
	     | Var Int
	     | Constant Int [JboTerm]
	     | Named String
	     | NonAnaph String
	     | UnboundSumbasti SumtiAtom
	     | JboQuote ParsedQuote
	     | JboErrorQuote [String]
	     | JboNonJboQuote String
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
	    | Moi Quantifier Cmavo
	    | Among JboTerm
	    | Equal
	    | UnboundBribasti TanruUnit
	    | TagRel JboTag -- xo'i
	    | Brivla String

data JboOperator
    = JboTagged JboTag (Maybe JboTerm)
    | QTruthModal
    | WithEventAs JboTerm
type JboTag = AbsTag Quantifier JboPred
type JboDecoratedTagUnit = DecoratedAbsTagUnit Quantifier JboPred
type JboTagUnit = AbsTagUnit Quantifier JboPred
type JboConnective = AbsConnective JboTag

type JboPred = JboTerm -> JboProp

type Abstractor = String

instance FOL.Term JboTerm where
    var n = BoundVar n

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
    subTermInTerm (QualifiedTerm qual t) = QualifiedTerm qual (subTermInTerm t)
    subTermInTerm (Constant n ts) = Constant n $ map subTermInTerm ts
    subTermInTerm x = if x == s then t else x
    subTermInRel (Tanru p r) = Tanru (subTermInPred p) (subTermInRel r)
    subTermInRel (TanruConnective con p p') = TanruConnective con (subTermInPred p) (subTermInPred p')
    subTermInRel (AbsPred a p) = AbsPred a (\o -> subTerm s t (p o))
    subTermInRel (AbsProp a p) = AbsProp a (subTerm s t p)
    subTermInRel (Among t) = Among $ subTermInTerm t
    subTermInRel r = r
    subTermInOp (JboTagged tag mt) =
	JboTagged (subTermInTag tag) $ if mt == Just s then Just t else mt
    subTermInOp (WithEventAs x) = WithEventAs $ subTermInTerm x
    subTermInOp op = op
    subTermInTag (ConnectedTag conn tag1 tag2) =
	ConnectedTag conn (subTermInTag tag1) (subTermInTag tag2)
    subTermInTag (DecoratedTagUnits dtus) = DecoratedTagUnits $ map subTermInDTU dtus
    subTermInDTU (DecoratedTagUnit nahe se nai tu) = DecoratedTagUnit nahe se nai $ subTermInTagUnit tu
    subTermInTagUnit (FIhO fiho) = FIhO $ subTermInPred fiho
    subTermInTagUnit tu = tu
    subTermInPred p = \x -> subTerm s t (p x)

-- TODO: would be neater to make a proper Traversable instance, such that
-- subTerm above could use it too - but I'm not sure how to handle quantifiers
class Termful t where
    --traverseTerms :: Applicative f => (JboTerm -> f JboTerm) -> t -> f t
    traverseTerms_ :: Applicative f => (JboTerm -> f ()) -> t -> f ()
    --traverseTerms_ f = (\x -> ()) <$> traverseTerms (\t -> f t *> pure (Var 0))
instance (Termful r, Termful o) => Termful (Prop r JboTerm c o) where
    traverseTerms_ f (Rel r ts) = traverseTerms_ f r *> traverse_ f ts
    traverseTerms_ f (Quantified q r p) =
	case r of {Nothing -> pure (); Just r' -> traverseTerms_ f (r' 0)}
	*> traverseTerms_ f (p 0)
    traverseTerms_ f (Not p) = traverseTerms_ f p
    traverseTerms_ f (Connected c p1 p2) = traverseTerms_ f p1 *> traverseTerms_ f p2
    traverseTerms_ f (NonLogConnected c p1 p2) = traverseTerms_ f p1 *> traverseTerms_ f p2
    traverseTerms_ f Eet = pure ()
    traverseTerms_ f (Modal o p) = traverseTerms_ f o *> traverseTerms_ f p
instance Termful JboRel where
    traverseTerms_ f (Tanru p r) = traverseTerms_ f p *> traverseTerms_ f r
    traverseTerms_ f (TanruConnective con p p') = traverseTerms_ f p *> traverseTerms_ f p'
    traverseTerms_ f (AbsPred a p) = traverseTerms_ f p
    traverseTerms_ f (AbsProp a p) = traverseTerms_ f p
    traverseTerms_ f (Among t) = f t
    traverseTerms_ f _ = pure ()
instance Termful JboPred where traverseTerms_ f p = traverseTerms_ f $ p ZoheTerm
instance Termful JboOperator where
    traverseTerms_ f (JboTagged tag mt) = traverseTerms_ f tag *> traverse_ f mt
    traverseTerms_ f (WithEventAs x) = f x
instance Termful JboTag where
    traverseTerms_ f (ConnectedTag conn tag1 tag2) = traverseTerms_ f tag1 *> traverseTerms_ f tag2
    traverseTerms_ f (DecoratedTagUnits dtus) = traverse_ (traverseTerms_ f) dtus
instance Termful JboDecoratedTagUnit where traverseTerms_ f (DecoratedTagUnit nahe se nai tu) = traverseTerms_ f tu
instance Termful JboTagUnit where
    traverseTerms_ f (FIhO fiho) = traverseTerms_ f fiho
    traverseTerms_ f _ = pure ()

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
