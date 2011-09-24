module Lojban where

import FOL hiding (Prop, Term, Connective)
import qualified FOL (Prop, Term, Connective)

import Data.Maybe
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

type Prop = FOL.Prop JboRel JboTerm

data JboTerm = SingVar Int
	     | Named String
	     | NonAnaph String
	     | ZoheTerm (Maybe (JboTerm -> Prop))

type Individual = Int

type Obj = JboTerm

type JboRel = String

instance Rel JboRel where
    relstr = id

isAmong :: JboTerm -> (JboTerm -> Prop)
isAmong y = \o -> Rel "me" [o,y]

instance FOL.Term JboTerm where
    singvar n = SingVar n
    objlogstr (SingVar 0) = "_"
    objlogstr (SingVar n) = "x" ++ (show n)
    objlogstr (Named s) = s
    objlogstr (NonAnaph ps) = ps
    objlogstr (ZoheTerm Nothing) = "zo'e"
    objlogstr (ZoheTerm (Just p)) = "zo'e:(" ++ show (p (SingVar 0)) ++ ")"

    objjbostr (ZoheTerm (Just p)) = "zo'e noi " ++ jboshow (p (SingVar 0)) ++ " ku'o"
    objjbostr (SingVar 0) = "ke'a"
    objjbostr (SingVar 1) = "da"
    objjbostr (SingVar 2) = "de"
    objjbostr (SingVar 3) = "di"
    objjbostr (SingVar 4) = "da xi vo"
    objjbostr (SingVar 5) = "da xi mu"
    objjbostr (SingVar 6) = "da xi xa"
    objjbostr o = objlogstr o

instance Show JboTerm where
    show t = objlogstr t

instance JboShow Prop
    where jboshow p = unwords $ jboshow' [] 1 p
	   where
	    jboshow' :: [String] -> Int -> Prop -> [String]
	    jboshow' ps n (Quantified q r p) =
	      let relstr = case r of
		    Nothing -> []
		    Just r' -> ["poi"] ++ jboshow' [] (n+1) (r' n)
	      in jboshow' (ps ++ [jboshow q, objjbostr $ SingVar n]
			    ++ relstr)
			  (n+1) (p n)
	    jboshow' ps n p | ps /= [] =
		ps ++ ["zo'u"] ++ (jboshow' [] n p)
	    jboshow' ps n (Connected c p1 p2) =
		case c of And -> ["ge"]
			  Or -> ["ga"]
			  Impl -> ["ga", "nai"]
			  Equiv -> ["go"]
		++ (jboshow' ps n p1) ++ ["gi"] ++ (jboshow' ps n p2)
	    jboshow' ps n (Not p) =
		["na","ku"] ++ (jboshow' ps n p)
	    jboshow' ps n (Rel r ts) =
		(map objjbostr ts)++[relstr r]
	    jboshow' ps n Eet = ["jitfa"]

data Subsentence =
    Subsentence {prenex::[Term], terms::[Term], bridiTail::BridiTail}
    deriving (Eq, Show, Ord)

data Term = Sumti Tag Sumti
	  | Negation
	  deriving (Eq, Show, Ord)
data Tag = Untagged
	 | FA Int
	 deriving (Eq, Show, Ord)
data Sumti = ConnectedSumti Connective Sumti Sumti
	   | QAtom (Maybe Quantifier) [RelClause] SumtiAtom
	   | QSelbri Quantifier [RelClause] Selbri
	   deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Term  -- goi
	       deriving (Eq, Show, Ord)
data SumtiAtom = Name String
	       | Variable Int -- da
	       | NonAnaphoricProsumti String -- mi
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       | Description Gadri Selbri
	       | Assignable Int -- ko'a
	       | Ri -- ri
	       | Zohe -- zo'e
	       deriving (Eq, Show, Ord)

type Gadri = String

data Connective = Connective Bool Char Bool
		deriving (Eq, Show, Ord)

data BridiTail = ConnectedBT Connective BridiTail BridiTail
	       | BridiTail3 Selbri [Term]
	       | GekSentence GekSentence
	       deriving (Eq, Show, Ord)

data GekSentence = ConnectedGS Connective Subsentence Subsentence [Term]
		 | NegatedGS GekSentence
		 deriving (Eq, Show, Ord)

data Selbri = TanruUnit TanruUnit2 [Term]
	    | Negated Selbri
	    deriving (Eq, Show, Ord)

data TanruUnit2 = Brivla String
	        | Permuted Int TanruUnit2
	        deriving (Eq, Show, Ord)

class SumtiTermType a where term :: Tag -> a -> Term

instance SumtiTermType Sumti where term tag x = Sumti tag x
instance SumtiTermType SumtiAtom where term tag x = term tag (QAtom Nothing [] x)

connToFOL :: Connective -> Prop -> Prop -> Prop
connToFOL (Connective True 'e' True) p1 p2 = Connected And p1 p2
connToFOL (Connective True 'a' True) p1 p2 = Connected Or p1 p2
connToFOL (Connective False 'a' True) p1 p2 = Connected Impl p1 p2
connToFOL (Connective True 'a' False) p1 p2 = Connected Impl p2 p1
connToFOL (Connective True 'o' True) p1 p2 = Connected Equiv p1 p2
connToFOL (Connective True 'u' True) p1 p2 = p1
connToFOL (Connective True 'U' True) p1 p2 = p2
connToFOL (Connective False c b2) p1 p2 =
    connToFOL (Connective True c b2) (Not p1) p2
connToFOL (Connective b1 c False) p1 p2 =
    connToFOL (Connective b1 c True) p1 (Not p2)

extendTail :: BridiTail -> [Term] -> BridiTail
extendTail (BridiTail3 sb tts) ts = BridiTail3 sb (tts++ts)
extendTail (ConnectedBT con bt1 bt2) ts =
    ConnectedBT con (extendTail bt1 ts)
                    (extendTail bt2 ts)
extendTail (GekSentence gs) ts =
    GekSentence (extendTailGS gs ts)
	where extendTailGS (ConnectedGS con s1 s2 tts) ts = 
		ConnectedGS con s1 s2 (tts++ts)
	      extendTailGS (NegatedGS gs) ts = NegatedGS (extendTailGS gs ts)

type Bindings = Map SumtiAtom JboTerm
type ImplicitVars = [SumtiAtom]

type JboPred = JboTerm -> Prop

data Arglist = Arglist {args :: [Obj], position::Int}
		deriving (Show)
appendToArglist :: Arglist -> Obj -> Arglist
appendToArglist as@(Arglist os n) o = Arglist (setArg os n o) (n+1)
setArg :: [Obj] -> Int -> Obj -> [Obj]
setArg os n o =
    let (a,b) = splitAt (n-1) os
	in case b of [] -> a++(replicate ((n-1)-(length a)) (ZoheTerm Nothing))++[o]
		     (_:bs) -> a++[o]++bs
swapArgs :: [Obj] -> Int -> Int -> [Obj]
swapArgs os n m =
    let lookupArg k = if k <= length os then os!!(k-1) else (ZoheTerm Nothing)
	a = lookupArg n
	b = lookupArg m
	in setArg (setArg os m a) n b

newArglist :: Arglist
newArglist = Arglist [] 1

sentToProp :: Subsentence -> ImplicitVars -> Bindings -> Prop
sentToProp (Subsentence ps ts bt) vs bs = sentToProp' ps ts bt vs bs newArglist

sentToProp' :: [Term] -> [Term] -> BridiTail -> ImplicitVars -> Bindings -> Arglist -> Prop
--sentToProp' a b c d e | trace ("sentToProp': "
--    ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d ++ " " ++
--	show e ) False = undefined
--
sentToProp' ps ts (ConnectedBT con bt1 bt2) vs bs as =
    let p1 = sentToProp' ps ts bt1 vs bs as
	p2 = sentToProp' ps ts bt2 vs bs as
	in connToFOL con p1 p2

sentToProp' ps ts (BridiTail3 (Negated sb) tts) vs bs as =
    Not $ sentToProp' ps ts (BridiTail3 sb tts) vs bs as

sentToProp' [] [] bt (v:vs) bs as =
    sentToProp' [] [term Untagged v] bt vs bs as

sentToProp' [] [] (BridiTail3 sb tts) vs bs as | tts /= [] =
    let as' = case (args as) of [] -> (Arglist [] 2) 
				_  -> as
	in sentToProp' [] tts (BridiTail3 sb []) vs bs as'

sentToProp' [] [] (GekSentence (ConnectedGS con s1 s2 tts)) vs bs as =
    let p1 = sentToProp'
		(prenex s1) (terms s1) (extendTail (bridiTail s1) tts) vs bs as
	p2 = sentToProp'
		(prenex s2) (terms s2) (extendTail (bridiTail s2) tts) vs bs as
	in connToFOL con p1 p2

sentToProp' [] [] (GekSentence (NegatedGS gs)) vs bs as =
    Not $ sentToProp' [] [] (GekSentence gs) vs bs as

sentToProp' [] [] (BridiTail3 (TanruUnit tu las) []) vs bs as =
    case tu of Brivla bv -> Rel bv (args as)
	       Permuted s tu ->
		   let (Arglist os n) = as in
		       sentToProp' [] [] (BridiTail3 (TanruUnit tu las) []) vs bs
			(Arglist (swapArgs os 1 s) n)

sentToProp' [] (t:ts) bt vs bs as =
 let argAppended vs bs tag o =
	 let as' = case tag of Untagged -> as
			       FA n -> as{position=n}
	     as'' = appendToArglist as' o
	     vs' = case o of SingVar v -> case Map.lookup (RelVar 1) bs of
					     Just (SingVar v) ->
						delete (RelVar 1) vs
					     _ -> vs
			     _ -> vs
	 in sentToProp' [] ts bt vs' bs as''
 in case t of
	 Negation -> sentToProp' [t] ts bt vs bs as
	 Sumti tag (ConnectedSumti con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti tag s1):ts) bt vs bs as
		    p2 = sentToProp' [] ((Sumti tag s2):ts) bt vs bs as
		    in connToFOL con p1 p2
	 Sumti tag s@(QAtom q rels sa) ->
	     let
		rrels = [evalRel subs bs | rel@(Restrictive subs) <- rels ]
		irels = [evalRel subs bs | rel@(Incidental subs) <- rels ]
		(p, incBit) = case sa of
		  Variable n ->
		      case (Map.lookup (Variable n) bs) of
			   Nothing ->
			       -- export to prenex:
			       (sentToProp' [term Untagged s]
				(term tag (Variable n):ts) bt vs bs as, Nothing)
			   Just o ->
			       (argAppended vs bs tag o, Just (irels, o))
		  rv@(RelVar _) ->
		      let Just o = (Map.lookup rv bs)
		      in (argAppended (delete rv vs) bs tag o, Just (irels, o))
		  _ -> -- rest are "plural"
		      let (o,irels') = case sa of
			     NonAnaphoricProsumti ps -> (NonAnaph ps, irels)
			     Name s -> (Named s, irels)
			     Zohe -> (zoheExpr irels, [])
			     Description "lo" sb ->
				 (zoheExpr (selbriToPred sb bs:irels), [])
			     where zoheExpr [] = ZoheTerm Nothing
				   zoheExpr irels =
				       ZoheTerm (Just $ andPred irels)
		     in case q of
			 Nothing -> (argAppended vs bs tag o, Just (irels', o))
			 Just q' ->
			     (quantified q' (Just $ andPred (isAmong o:rrels))
				     (\o -> argAppended vs bs tag o),
				 Just (irels', o))
	    in case incBit of Nothing -> p
			      Just ([], _) -> p
			      Just (irels, o) ->
				  Connected And (andPred irels o) p
	 Sumti tag s@(QSelbri q rels sb) ->
	     let rrels = [evalRel subs bs | rel@(Restrictive subs) <- rels ]
		 irels = [evalRel subs bs | rel@(Incidental subs) <- rels ]
		 p = Just $ andPred (selbriToPred sb bs:rrels)
	     in quantified q p (andPred (argAppended vs bs tag:irels))
	    
sentToProp' (Negation:pts) ts bt vs bs as =
    Not $ sentToProp' pts ts bt vs bs as
sentToProp' (Sumti Untagged (QAtom q rels (Variable n)):pts) ts bt vs bs as =
	quantified (fromMaybe Exists q)
		   (case rels of [] -> Nothing
				 _  -> Just $ (\o ->
				     let bs' = Map.insert (Variable n) o bs
				     in bigAnd (map (\(Restrictive subs) ->
					 evalRel subs bs' o) rels)))
		   (\o -> sentToProp' pts ts bt vs
			   (Map.insert (Variable n) o bs) as)

quantified :: Quantifier -> Maybe JboPred -> JboPred -> Prop
quantified q r p = Quantified q (case r of Nothing -> Nothing
				           Just r -> Just $ singpred r)
				(singpred p)
    where singpred p = \v -> p (SingVar v)

selbriToRelClauseBridiTail :: Selbri -> BridiTail
selbriToRelClauseBridiTail (Negated sb) =
    let BridiTail3 sb' tts = selbriToRelClauseBridiTail sb
    in BridiTail3 (Negated sb') tts
selbriToRelClauseBridiTail (TanruUnit tu las) =
    BridiTail3 (TanruUnit tu []) las

selbriToPred :: Selbri -> Bindings -> JboPred
selbriToPred sb bs = evalRel (Subsentence [] [] bt) bs
    where bt = selbriToRelClauseBridiTail sb

evalRel :: Subsentence -> Bindings -> JboPred
evalRel subs bs = \o ->
    sentToProp subs [rv] (Map.insert rv o (shuntVars bs RelVar))
	where rv = RelVar 1

shuntVars :: Bindings -> (Int -> SumtiAtom) -> Bindings
shuntVars bs var = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 0 .. head [ n | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]
