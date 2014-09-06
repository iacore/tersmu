module JboSyntax where
import FOL hiding (Term, Connective)
-- Abstract syntax:
data Statement = Statement [FreeIndex] [Term] Statement1
    deriving (Eq, Show, Ord)

data LogJboConnective = LogJboConnective Bool Char Bool
		deriving (Eq, Show, Ord)

data Statement1 = ConnectedStatement Connective Statement1 Statement1
		| StatementSentence Sentence
		| StatementStatements [Statement]
		deriving (Eq, Show, Ord)

data Subsentence = Subsentence [FreeIndex] [Term] Sentence
    deriving (Eq, Show, Ord)

data Sentence = Sentence [Term] BridiTail
    deriving (Eq, Show, Ord)

data Free
    = Bracketed [Statement]
    | Discursive BridiTail
    | TruthQ (Maybe Int)
    | Vocative [COI] (Maybe Sumti)
    | MAI Mex
    | XI Mex
    | Indicator {indicatorNai :: Bool, indicatorCmavo :: Cmavo}
    deriving (Eq, Show, Ord)

data COI = COI {coiCOI::String, coiNAI::Bool}
    deriving (Eq, Show, Ord)

type FreeIndex = Int

data Term = Sumti Tagged Sumti
	  | Negation
	  | Termset [Term]
	  | ConnectedTerms Bool Connective Term Term
	  | BareTag Tag
	  | BareFA (Maybe Int)
	  deriving (Eq, Show, Ord)

data Tagged = Untagged
	 | Tagged Tag
	 | FATagged Int
	 | FAITagged
	 deriving (Eq, Show, Ord)

data AbsTag r t
    = DecoratedTagUnits [DecoratedAbsTagUnit r t]
    | ConnectedTag (AbsConnective r t) (AbsTag r t) (AbsTag r t)
    deriving (Eq, Show, Ord)
data DecoratedAbsTagUnit r t = DecoratedTagUnit
    {tagNahe::Maybe Cmavo, tagSE::Maybe Int, tagNAI::Bool, tagUnit::AbsTagUnit r t}
    deriving (Eq, Show, Ord)
data AbsTagUnit r t
    = TenseCmavo Cmavo
    | FAhA {fahaHasMohi::Bool, fahaCmavo::Cmavo}
    | ROI {roiroi::Cmavo, roiIsSpace::Bool, roiQuantifier::AbsMex r t}
    | TAhE_ZAhO {taheZoheIsSpace::Bool, taheZahoCmavo::Cmavo}
    | BAI Cmavo
    | FIhO r
    | CUhE
    | KI
    deriving (Eq, Show, Ord)

type Tag = AbsTag Selbri Sumti
type DecoratedTagUnit = DecoratedAbsTagUnit Selbri Sumti
type TagUnit = AbsTagUnit Selbri Sumti

data AbsConnective r t
    = JboConnLog (Maybe (AbsTag r t)) LogJboConnective
    | JboConnJoik (Maybe (AbsTag r t)) Joik
    deriving (Eq, Show, Ord)
type Connective = AbsConnective Selbri Sumti

type Joik = String

-- XXX we arbitarily consider a mix of tense and "modal" to be a tense
isTense :: AbsTag r t -> Bool
isTense (ConnectedTag _ t1 t2) = isTense t1 || isTense t2
isTense (DecoratedTagUnits dtus) = or $ map isTenseDTU dtus
    where isTenseDTU (DecoratedTagUnit _ _ _ tu) = case tu of
	    BAI _ ->  False
	    FIhO _ -> False
	    _ -> True

type Cmavo = String

data Sumti = ConnectedSumti Bool Connective Sumti Sumti [RelClause]
	   | QAtom (Maybe Mex) [RelClause] SumtiAtom
	   | QSelbri Mex [RelClause] Selbri
	   deriving (Eq, Show, Ord)

appendRelsToSumti newrels (ConnectedSumti fore con s1 s2 rels) =
    ConnectedSumti fore con s1 s2 (rels++newrels)
appendRelsToSumti newrels (QAtom q rels sa) =
    QAtom q (rels++newrels) sa
appendRelsToSumti newrels (QSelbri q rels s) =
    QSelbri q (rels++newrels) s

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Term  -- goi
	       | RestrictiveGOI String Term  -- pe etc.
	       | IncidentalGOI String Term  -- ne etc.
	       deriving (Eq, Show, Ord)

data SumtiAtom = Name [RelClause] String
	       | Variable Int -- da
	       | NonAnaphoricProsumti String -- mi
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       | SelbriVar -- fake
	       | Description Gadri (Maybe Sumti) (Maybe Mex) (Either Selbri Sumti) [RelClause] [RelClause]
	       | Assignable Int -- ko'a
	       | LerfuString [Lerfu]
	       | Ri Int -- ri
	       | Ra Cmavo -- ra/ru
	       | MainBridiSumbasti Int -- vo'a
	       | Quote [Statement]
	       | NonJboQuote String
	       | ErrorQuote [String]
	       | Word String
	       | MexLi Mex -- li
	       | MexMex Mex -- mo'e
	       | Zohe -- zo'e
	       | SumtiQ (Maybe Int) -- ma [kau]
	       | QualifiedSumti SumtiQualifier [RelClause] Sumti
	       deriving (Eq, Show, Ord)

-- TODO properly
newtype Lerfu = Lerfu Char
    deriving (Eq, Show, Ord)
lerfuToChar :: Lerfu -> Maybe Char
lerfuToChar (Lerfu c) = Just c

type Gadri = String

getsRi :: SumtiAtom -> Bool
getsRi Zohe = False
getsRi (Assignable _) = False
getsRi (LerfuString _) = False
getsRi (MainBridiSumbasti _) = False
getsRi (Variable _) = False
getsRi (NonAnaphoricProsumti p) = p `elem` ["ti","ta","tu"]
getsRi _ = True

isAssignable :: SumtiAtom -> Bool
isAssignable (Assignable _) = True
isAssignable (LerfuString _) = True
isAssignable (Name _ _) = True
isAssignable _ = False

data SumtiQualifier = LAhE String | NAhE_BO String
    deriving (Eq, Show, Ord)

data BridiTail = ConnectedBT Connective BridiTail BridiTail [Term]
	       | BridiTail3 Selbri [Term]
	       | GekSentence GekSentence
	       deriving (Eq, Show, Ord)

data GekSentence = ConnectedGS Connective Subsentence Subsentence [Term]
		 | TaggedGS Tag GekSentence
		 | NegatedGS GekSentence
		 deriving (Eq, Show, Ord)

data Selbri = Negated Selbri
	    | TaggedSelbri Tag Selbri
	    | Selbri2 Selbri2
	    deriving (Eq, Show, Ord)

data Selbri2 = SBInverted Selbri3 Selbri2
	     | Selbri3 Selbri3
	     deriving (Eq, Show, Ord)

data Selbri3 = SBTanru Selbri3 Selbri3
	     | ConnectedSB Bool Connective Selbri Selbri3
	     | BridiBinding Selbri3 Selbri3
	     | ScalarNegatedSB NAhE Selbri3
	     | TanruUnit TanruUnit [Term]
	     deriving (Eq, Show, Ord)

type NAhE = Cmavo

sb3tosb :: Selbri3 -> Selbri
sb3tosb = Selbri2 . Selbri3

data TanruUnit = TUBrivla String
		| TUGOhA String Int
		| TUMe Sumti
		| TUMoi Sumti String
		| TUAbstraction Abstractor Subsentence
	        | TUPermuted Int TanruUnit
		| TUJai (Maybe Tag) TanruUnit
		| TUXOhI Tag
		| TUSelbri3 Selbri3
	        deriving (Eq, Show, Ord)

data Abstractor
    = NU Cmavo
    | NegatedAbstractor Abstractor
    -- Note: tagged connectives aren't allowed with NU, which makes things simpler
    -- (but less uniform...)
    | LogConnectedAbstractor LogJboConnective Abstractor Abstractor
    | JoiConnectedAbstractor Joik Abstractor Abstractor
    deriving (Eq, Show, Ord)

data AbsMex r t
    = Operation (AbsOperator r t) [AbsMex r t]
    | ConnectedMex Bool (AbsConnective r t) (AbsMex r t) (AbsMex r t)
    | QualifiedMex SumtiQualifier (AbsMex r t)
    | MexInt Int
    | MexNumeralString [Numeral]
    | MexLerfuString [Lerfu]
    | MexSelbri r
    | MexSumti t
    | MexArray [AbsMex r t]
    deriving (Eq, Show, Ord)

type Mex = AbsMex Selbri Sumti

mexIsNumberOrLS (MexInt _) = True
mexIsNumberOrLS (MexNumeralString _) = True
mexIsNumberOrLS (MexLerfuString _) = True
mexIsNumberOrLS _ = False

data Numeral = PA Cmavo | NumeralLerfu Lerfu
    deriving (Eq, Show, Ord)

data AbsOperator r t
    = ConnectedOperator Bool (AbsConnective r t) (AbsOperator r t) (AbsOperator r t)
    | OpPermuted Int (AbsOperator r t)
    | OpScalarNegated NAhE (AbsOperator r t)
    | OpMex (AbsMex r t)
    | OpSelbri r
    | OpVUhU Cmavo
    deriving (Eq, Show, Ord)

type Operator = AbsOperator Selbri Sumti

lerfuStringOfSelbri :: Selbri -> [Lerfu]
lerfuStringOfSelbri (Negated sb) = lerfuStringOfSelbri sb
lerfuStringOfSelbri (TaggedSelbri _ sb) = lerfuStringOfSelbri sb
lerfuStringOfSelbri (Selbri2 sb2) = sb2tols sb2
    where
	sb2tols (SBInverted sb3 sb2) = sb3tols sb3 ++ sb2tols sb2
	sb2tols (Selbri3 sb3) = sb3tols sb3
	sb3tols (SBTanru sb sb') = sb3tols sb ++ sb3tols sb'
	sb3tols (ConnectedSB _ _ sb sb3) = sbtols sb ++ sb3tols sb3
	sb3tols (BridiBinding sb3 _) = sb3tols sb3
	sb3tols (TanruUnit tu _) = tutols tu
	sbtols = lerfuStringOfSelbri
	tutols (TUBrivla s) = map Lerfu $ take 1 s
	tutols (TUAbstraction (NU s) _) = map Lerfu $ take 1 s
	tutols (TUSelbri3 sb3) = sb3tols sb3
	tutols _ = []

{-
class Bifunctor p where
    bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
instance Bifunctor AbsMex where
    bimap fr ft = bimap' where
	bimap' (Operation o ms) = Operation (bimap' o) (map bimap' ms)
	bimap' (ConnectedMex f c m1 m2) = ConnectedMex f (bimap' c) (bimap' m1) (bimap' m2)
	bimap' (QualifiedMex q m) = QualifiedMex q (bimap' m)
	bimap' (MexArray ms) = MexArray $ map bimap' ms
	bimap' (MexSelbri r) = MexSelbri $ fr r
	bimap' (MexSumti t) = MexSumti $ ft t
	bimap' x = x
    
instance Bifunctor AbsOperator where
    bimap fr ft = bimap' where
	bimap' (ConnectedOperator f c o1 o2) = ConnectedOperator f (bimap' c) (bimap' o1) (bimap' o2)
	bimap' (OpPermuted s o) = OpPermuted s $ bimap' o
	bimap' (OpScalarNegated n o) = OpScalarNegated n $ bimap' o
	bimap' (OpMex m) = OpMex $ bimap' m
	bimap' (OpSelbri r) = OpSelbri $ fr r
	bimap' x = x
-}
