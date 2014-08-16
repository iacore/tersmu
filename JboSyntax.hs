module JboSyntax where
import FOL hiding (Term)
-- Abstract syntax:
data Statement = Statement [Term] Statement1
    deriving (Eq, Show, Ord)

data JboConnective = JboConnective Bool Char Bool
		deriving (Eq, Show, Ord)

data Statement1 = ConnectedStatement JboConnective Statement1 Statement1
		| StatementSentence Sentence
		| StatementStatements [Statement]
		deriving (Eq, Show, Ord)

data Subsentence = Subsentence [Term] Sentence
    deriving (Eq, Show, Ord)

data Sentence = Sentence [Term] BridiTail
    deriving (Eq, Show, Ord)

data Term = Sumti Tagged Sumti
	  | Negation
	  | Termset [Term]
	  | ConnectedTerms JboConnective Term Term
	  | BareTag Tag
	  deriving (Eq, Show, Ord)

data Tagged = Untagged
	 | Tagged Tag
	 | FATagged Int
	 deriving (Eq, Show, Ord)

data AbsTag q fiho
    = TagUnit {tagNahe::Maybe Cmavo, tagSE::Maybe Int, tagNAI::Bool, tagUnit::AbsTagUnit q fiho}
    | ConnectedTag JboConnective (AbsTag q fiho) (AbsTag q fiho)
instance (Eq q, Eq fiho) => Eq (AbsTag q fiho)
instance (Show q, Show fiho) => Show (AbsTag q fiho)
instance (Ord q, Ord fiho) => Ord (AbsTag q fiho)
data AbsTagUnit q fiho
    = TenseCmavo Cmavo
    | FAhA {fahaHasMohi::Bool, fahaCmavo::Cmavo}
    | ROI {roiIsSpace::Bool, roiQuantifier::q}
    | TAhE_ZAhO {taheZoheIsSpace::Bool, taheZahoCmavo::Cmavo}
    | BAI Cmavo
    | FIhO fiho
    | CUhE
    | KI

type Tag = AbsTag Quantifier Selbri
type TagUnit = AbsTagUnit Quantifier Selbri

type Cmavo = String

data Sumti = ConnectedSumti JboConnective Sumti Sumti [RelClause]
	   | QAtom (Maybe Quantifier) [RelClause] SumtiAtom
	   | QSelbri Quantifier [RelClause] Selbri
	   deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Sumti  -- goi
	       | RestrictiveGOI String Sumti  -- pe etc.
	       | IncidentalGOI String Sumti  -- ne etc.
	       deriving (Eq, Show, Ord)

data SumtiAtom = Name String
	       | Variable Int -- da
	       | NonAnaphoricProsumti String -- mi
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       | SelbriVar -- fake
	       | Description Gadri (Maybe Sumti) (Maybe Quantifier) Selbri [RelClause] [RelClause]
	       | Assignable Int -- ko'a
	       | LerfuString [Lerfu]
	       | Ri -- ri
	       | Quote [Statement]
	       | Word String
	       | Zohe -- zo'e
	       deriving (Eq, Show, Ord)

type Lerfu = Char

type Gadri = String

data BridiTail = ConnectedBT JboConnective BridiTail BridiTail [Term]
	       | BridiTail3 Selbri [Term]
	       | GekSentence GekSentence
	       deriving (Eq, Show, Ord)

data GekSentence = ConnectedGS JboConnective Subsentence Subsentence [Term]
		 | NegatedGS GekSentence
		 deriving (Eq, Show, Ord)

data Selbri = Negated Selbri
	    | Selbri2 Selbri2
	    deriving (Eq, Show, Ord)

data Selbri2 = SBInverted Selbri3 Selbri2
	     | Selbri3 Selbri3
	     deriving (Eq, Show, Ord)

data Selbri3 = SBTanru Selbri3 Selbri3
	     | ConnectedSB JboConnective Selbri3 Selbri3
	     | BridiBinding Selbri3 Selbri3
	     | TanruUnit TanruUnit2 [Term]
	     deriving (Eq, Show, Ord)

data TanruUnit2 = TUBrivla String
		| TUGOhA String
		| TUMe Sumti
		| TUMoi Quantifier String
		| TUAbstraction String Subsentence
	        | TUPermuted Int TanruUnit2
		| TUSelbri3 Selbri3
	        deriving (Eq, Show, Ord)

appendRelsToSumti newrels (ConnectedSumti con s1 s2 rels) =
    ConnectedSumti con s1 s2 (rels++newrels)
appendRelsToSumti newrels (QAtom q rels sa) =
    QAtom q (rels++newrels) sa
appendRelsToSumti newrels (QSelbri q rels s) =
    QSelbri q (rels++newrels) s
