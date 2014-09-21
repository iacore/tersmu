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
	     | PredNamed JboPred
	     | NonAnaph String
	     | UnboundSumbasti SumtiAtom
	     | JboQuote ParsedQuote
	     | JboErrorQuote [String]
	     | JboNonJboQuote String
	     | TheMex Mex -- me'o
	     | Value JboMex -- li
	     | Valsi String
	     | Unfilled
	     | JoikedTerms Joik JboTerm JboTerm
	     | QualifiedTerm SumtiQualifier JboTerm
	     deriving (Eq, Show, Ord)

data JboRel = Tanru JboVPred JboRel
	    | TanruConnective JboConnective JboVPred JboVPred
	    | ScalarNegatedRel NAhE JboRel
	    | AbsPred Abstractor JboNPred
	    | AbsProp Abstractor JboProp
	    | Moi JboTerm Cmavo
	    | Among JboTerm
	    | Equal
	    | UnboundBribasti TanruUnit
	    | BoundRelVar Int
	    | OperatorRel JboOperator
	    | TagRel JboTag -- xo'i
	    | Brivla String
    deriving (Eq, Show, Ord)

data JboModalOp
    = JboTagged JboTag (Maybe JboTerm)
    | WithEventAs JboTerm
    | QTruthModal
    | NonVeridical
type JboTag = AbsTag JboVPred JboTerm
type JboDecoratedTagUnit = DecoratedAbsTagUnit JboVPred JboTerm
type JboTagUnit = AbsTagUnit JboVPred JboTerm
type JboConnective = AbsConnective JboVPred JboTerm

-- variadic, n-ary, and unary predicates
type JboVPred = [JboTerm] -> JboProp
data JboNPred = JboNPred Int ([JboTerm] -> JboProp)
type JboPred = JboTerm -> JboProp
vPredToPred vp o = vp [o]
predToNPred p = JboNPred 1 (\(o:_) -> p o)

jboPredToLojPred :: JboPred -> (Int -> JboProp)
jboPredToLojPred r = \v -> r (BoundVar v)

type JboMex = AbsMex JboVPred JboTerm
type JboOperator = AbsOperator JboVPred JboTerm

data JboQuantifier
    = MexQuantifier JboMex
    | LojQuantifier LojQuantifier
    | QuestionQuantifier
    | RelQuantifier JboQuantifier
    deriving (Eq, Show, Ord)

instance FOL.Term JboTerm where
    var n = BoundVar n

data JboFragment
    = JboFragTerms [JboTerm]
    | JboFragUnparsed Fragment
    deriving (Eq, Show, Ord)

type JboText = [Texticule]
data Texticule
    = TexticuleFrag JboFragment
    | TexticuleProp JboProp
    deriving (Eq, Show, Ord)
propTexticules :: [Texticule] -> [JboProp]
propTexticules [] = []
propTexticules (TexticuleProp p:ts) = p:propTexticules ts
propTexticules (_:ts) = propTexticules ts

-- |ParsedQuote: using this newtype so we can provide dummy instances for use
-- in derived instances for JboTerm
newtype ParsedQuote = ParsedQuote JboText
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
instance Eq JboVPred where { _ == _ = False }
instance Show JboVPred where { show _ = "[ \\[_] -> ... ]" }
instance Ord JboVPred where { _ <= _ = False }
instance Eq JboNPred where { _ == _ = False }
instance Show JboNPred where { show (JboNPred n _) = "[ \\_1,...,\\_"++show n++" -> ... ]" }
instance Ord JboNPred where { _ <= _ = False }

class Termful t where
    -- XXX: you'd think there would be a neat common abstraction of
    -- traverseTerms_ and subTerm, but I haven't found one
    -- (we can't just define a Traversable instance, due to the use of
    -- functions for quantifiers and JboPreds)

    -- |traverseTerms_ (travTs_ for short): apply an applicative to the terms
    traverseTerms_,travTs_ :: Applicative f => (JboTerm -> f ()) -> t -> f ()
    traverseTerms_ = travTs_ -- abbreviation
    travTs_ _ _ = pure () -- default definition

    travtravTs_ :: (Termful t, Applicative f, Foldable fo) =>
	(JboTerm -> f()) -> fo t -> f ()
    travtravTs_ = traverse_ . traverseTerms_

    -- | subTerm s t: substitute all instances of s for t
    subTerm :: JboTerm -> JboTerm -> t -> t
    subTerm _ _ = id

{- correct, but useless due to overlapping instances
instance (Termful t, Foldable fo, Functor fo) => Termful (fo t) where
    traverseTerms_ = traverse_ . traverseTerms_
    subTerm s t = fmap $ subTerm s t
-}

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
    subTerm s t = terpProp (\r -> \ts -> Rel (subTerm s t r) $ map (subTerm s t) ts) (subTerm s t) (subTerm s t)
instance Termful JboTerm where
    travTs_ f t = f t
    subTerm s t (JoikedTerms joik t1 t2) = JoikedTerms joik (subTerm s t t1) (subTerm s t t2)
    subTerm s t (QualifiedTerm qual t') = QualifiedTerm qual (subTerm s t t')
    subTerm s t (Constant n ts) = Constant n $ map (subTerm s t) ts
    subTerm s t (Value m) = Value $ subTerm s t m
    subTerm s t (PredNamed p) = PredNamed $ subTerm s t p
    subTerm s t x = if x == s then t else x
instance Termful FOL.Connective
instance Termful Joik
instance Termful JboQuantifier where
    travTs_ f (LojQuantifier q) = travTs_ f q
    travTs_ f (MexQuantifier m) = travTs_ f m
    travTs_ _ _ = pure ()
instance Termful LojQuantifier
instance Termful JboRel where
    travTs_ f (Tanru p r) = travTs_ f p *> travTs_ f r
    travTs_ f (TanruConnective con p1 p2) = travTs_ f con *> travtravTs_ f [p1,p2]
    travTs_ f (AbsPred a p) = travTs_ f p
    travTs_ f (AbsProp a p) = travTs_ f p
    travTs_ f (Among t) = f t
    travTs_ f (Moi t _) = f t
    travTs_ _ _ = pure ()
    subTerm s t (Tanru p r) = Tanru (subTerm s t p) (subTerm s t r)
    subTerm s t (TanruConnective con p p') = TanruConnective (subTerm s t con) (subTerm s t p) (subTerm s t p')
    subTerm s t (AbsPred a p) = AbsPred a $ subTerm s t p
    subTerm s t (AbsProp a p) = AbsProp a (subTerm s t p)
    subTerm s t (Among t') = Among $ (subTerm s t) t'
    subTerm s t (Moi t' m) = Moi ((subTerm s t) t') m
    subTerm s t r = r
instance Termful JboPred where
    travTs_ f p = travTs_ f $ p Unfilled
    subTerm s t p = \x -> subTerm s t (p x)
instance Termful JboVPred where
    travTs_ f p = travTs_ f $ p []
    subTerm s t p = \xs -> subTerm s t (p xs)
instance Termful JboNPred where
    travTs_ f (JboNPred arity p) = travTs_ f $ p $ replicate arity Unfilled
    subTerm s t (JboNPred arity p) = JboNPred arity $ \xs -> subTerm s t (p xs)
instance Termful JboModalOp where
    travTs_ f (JboTagged tag mt) = travTs_ f tag *> traverse_ f mt
    travTs_ f (WithEventAs x) = f x
    travTs_ f _ = pure ()
    subTerm s t (JboTagged tag mt) =
	JboTagged (subTerm s t tag) $ fmap (subTerm s t) mt
    subTerm s t (WithEventAs x) = WithEventAs $ subTerm s t x
    subTerm s t op = op
instance Termful JboTag where
    travTs_ f (ConnectedTag con tag1 tag2) = travTs_ f con *> travtravTs_ f [tag1,tag2]
    travTs_ f (DecoratedTagUnits dtus) = travtravTs_ f dtus
    subTerm s t (ConnectedTag con tag1 tag2) =
	ConnectedTag (subTerm s t con) (subTerm s t tag1) (subTerm s t tag2)
    subTerm s t (DecoratedTagUnits dtus) = DecoratedTagUnits $ map (subTerm s t) dtus
instance Termful JboDecoratedTagUnit where
    travTs_ f (DecoratedTagUnit nahe se nai tu) = travTs_ f tu
    subTerm s t (DecoratedTagUnit nahe se nai tu) = DecoratedTagUnit nahe se nai $ subTerm s t tu
instance Termful JboTagUnit where
    travTs_ f (FIhO fiho) = travTs_ f fiho
    travTs_ _ _ = pure ()
    subTerm s t (FIhO fiho) = FIhO $ subTerm s t fiho
    subTerm s t tu = tu
instance Termful JboConnective where
    travTs_ f (JboConnLog (Just tag) _) = travTs_ f tag
    travTs_ f (JboConnJoik (Just tag) _) = travTs_ f tag
    travTs_ _ _ = pure ()
    subTerm s t (JboConnLog (Just tag) lcon) = JboConnLog (Just $ subTerm s t tag) lcon
    subTerm s t (JboConnJoik (Just tag) joik) = JboConnJoik (Just $ subTerm s t tag) joik
    subTerm s t c = c
instance Termful JboMex where
    travTs_ f (Operation op ms) = travTs_ f op *> travtravTs_ f ms
    travTs_ f (ConnectedMex _ con m1 m2) = travTs_ f con *> travtravTs_ f [m1,m2]
    travTs_ f (QualifiedMex _ m) = travTs_ f m
    travTs_ f (MexSelbri r) = travTs_ f r
    travTs_ f (MexSumti t) = f t
    travTs_ f (MexArray ms) = travtravTs_ f ms
    travTs_ _ _ = pure ()
    subTerm s t (Operation op ms) = Operation (subTerm s t op) $ map (subTerm s t) ms
    subTerm s t (ConnectedMex f con m1 m2) = ConnectedMex f (subTerm s t con) (subTerm s t m1) (subTerm s t m2)
    subTerm s t (QualifiedMex q m) = QualifiedMex q $ subTerm s t m
    subTerm s t (MexSelbri r) = MexSelbri $ subTerm s t r
    subTerm s t (MexSumti t') = MexSumti $ subTerm s t t'
    subTerm s t (MexArray ms) = MexArray $ map (subTerm s t) ms
    subTerm s t m = m
instance Termful JboOperator where
    travTs_ f (ConnectedOperator _ con op1 op2) = travTs_ f con *> travtravTs_ f [op1,op2]
    travTs_ f (OpPermuted _ op) = travTs_ f op
    travTs_ f (OpScalarNegated _ op) = travTs_ f op
    travTs_ f (OpMex m) = travTs_ f m
    travTs_ f (OpSelbri r) = travTs_ f r
    travTs_ _ _ = pure ()
    subTerm s t (ConnectedOperator f con op1 op2) = ConnectedOperator f (subTerm s t con) (subTerm s t op1) (subTerm s t op2)
    subTerm s t (OpPermuted se op) = OpPermuted se $ subTerm s t op
    subTerm s t (OpScalarNegated n op) = OpScalarNegated n $ subTerm s t op
    subTerm s t (OpMex m) = OpMex $ subTerm s t m
    subTerm s t (OpSelbri r) = OpSelbri $ subTerm s t r
    subTerm s t op = op

freeVars :: JboProp -> [JboTerm]
freeVars p = execWriter $ collectFrees p where
	collectFrees = traverseTerms_ collectFreesInTerm
	collectFreesInTerm free@(Var _) = tell $ [free]
	collectFreesInTerm free@(UnboundSumbasti (MainBridiSumbasti _)) = tell $ [free]
	collectFreesInTerm (JoikedTerms joik t1 t2) = collectFreesInTerm t1 *> collectFreesInTerm t2
	collectFreesInTerm (QualifiedTerm qual t) = collectFreesInTerm t
	collectFreesInTerm (Constant _ ts) = traverse_ collectFreesInTerm ts
	collectFreesInTerm (Value m) = traverseTerms_ collectFreesInTerm m
	collectFreesInTerm (PredNamed p) = traverseTerms_ collectFreesInTerm p
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
