module Lojban where

import FOL hiding (Prop, Term)
import qualified FOL (Prop, Term)

import Data.Maybe
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

type Prop = FOL.Prop JboRel JboTerm

data JboTerm = SingVar Int
	     | SingConst Int
	     | Restricted (Obj -> Prop) JboTerm
	     | Described Gadri (Obj -> Prop)
	     | Named String
	     | Personal String
	     | Raw String
	     | ZoheTerm

type Individual = Int

type Obj = JboTerm

type JboRel = String

instance Rel JboRel where
    relstr = id

isAmong :: Obj -> (Obj -> Prop)
isAmong y = \x -> Rel "me" [x,y]

instance FOL.Term JboTerm where
    singvar n = SingVar n
    objlogstr (SingVar n) = "x" ++ (show n)
    objlogstr (SingConst n) = "c" ++ (show n)
    objlogstr (Named s) = s
    objlogstr (Personal ps) = ps
    objlogstr (Raw s) = s
    objlogstr ZoheTerm = "zo'e"
    objlogstr (Described g p) = g ++ " [" ++ show (p (Raw "_")) ++ "]"
    objlogstr (Restricted p t) = objlogstr t ++ ":" ++ show (p (Raw "_"))

    objjbostr (Described g p) = g ++ " [" ++ propToForeJbo (p (Raw "_")) ++ "] ku"
    objjbostr (Restricted p t) = objlogstr t ++
	" poi " ++ propToForeJbo (p (Raw "ke'a")) ++ " ku'o"
    -- XXX we don't handle nested variables properly here
    objjbostr (SingVar 1) = "da"
    objjbostr (SingVar 2) = "de"
    objjbostr (SingVar 3) = "di"
    objjbostr (SingVar 4) = "da xi vo"
    objjbostr (SingVar 5) = "da xi mu"
    objjbostr (SingVar 6) = "da xi xa"
    objjbostr o = objlogstr o

instance Show JboTerm where
    show t = objlogstr t

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
	       | PersonalProsumti String -- mi
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

type Quantifier = String

class SumtiTermType a where term :: Tag -> a -> Term

instance SumtiTermType Sumti where term tag x = Sumti tag x
instance SumtiTermType SumtiAtom where term tag x = term tag (QAtom Nothing [] x)

connToFOL :: Connective -> Prop -> Prop -> Prop
connToFOL (Connective True 'e' True) p1 p2 = And p1 p2
connToFOL (Connective True 'a' True) p1 p2 = Or p1 p2
connToFOL (Connective False 'a' True) p1 p2 = Impl p1 p2
connToFOL (Connective True 'a' False) p1 p2 = Impl p2 p1
connToFOL (Connective True 'o' True) p1 p2 = Equiv p1 p2
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

type Bindings = Map SumtiAtom Obj
type ImplicitVars = [SumtiAtom]

data Arglist = Arglist {args :: [Obj], position::Int}
		deriving (Show)
appendToArglist :: Arglist -> Obj -> Arglist
appendToArglist as@(Arglist os n) o = Arglist (setArg os n o) (n+1)
setArg :: [Obj] -> Int -> Obj -> [Obj]
setArg os n o =
    let (a,b) = splitAt (n-1) os
	in case b of [] -> a++(replicate ((n-1)-(length a)) ZoheTerm)++[o]
		     (_:bs) -> a++[o]++bs
swapArgs :: [Obj] -> Int -> Int -> [Obj]
swapArgs os n m =
    let lookupArg k = if k <= length os then os!!(k-1) else ZoheTerm
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
	     bs' = Map.insert (Ri) o bs
	 in sentToProp' [] ts bt vs bs' as''
 in case t of
	 Negation -> sentToProp' [t] ts bt vs bs as
	 Sumti tag (ConnectedSumti con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti tag s1):ts) bt vs bs as
		    p2 = sentToProp' [] ((Sumti tag s2):ts) bt vs bs as
		    in connToFOL con p1 p2
	 Sumti tag s@(QAtom q rels sa) ->
	     case sa of
		  Variable v ->
		      case (Map.lookup (Variable v) bs) of
			   Nothing ->
			       -- export to prenex:
			       sentToProp' [term Untagged s]
				(term tag (Variable v):ts) bt vs bs as
			   Just o ->
			       argAppended vs bs tag o
		  rv@(RelVar _) ->
		      let Just o = (Map.lookup rv bs)
		      in argAppended (delete rv vs) bs tag o
		  Ri ->
		      let Just o = (Map.lookup Ri bs)
		      in argAppended vs bs tag o
		  _ -> -- rest are "plural"
		     let o = case sa of
				 PersonalProsumti ps -> Personal ps
				 Name s -> Named s
				 Zohe -> ZoheTerm
				 Description g sb ->
				     Described g (selbriToPred sb bs)
			 rs = [ relToPred rel bs | rel@(Restrictive _) <- rels ]
			 o' = case rs of [] -> o
					 _  -> Restricted
						(\x -> bigAnd [ r x | r <- rs])
						o
		     in case q of
			 Nothing -> argAppended vs bs tag o
			 Just q' -> quantified q' (isAmong o')
				     (\x -> argAppended vs bs tag x)
	 Sumti tag s@(QSelbri q rels sb) ->
	     let rs = [ relToPred rel bs | rel@(Restrictive _) <- rels ]
		 p = (\x -> bigAnd ((selbriToPred sb bs x):[ r x | r <- rs]))
	     in quantified q p (\x -> argAppended vs bs tag x)
	    
sentToProp' (Negation:pts) ts bt vs bs as =
    Not $ sentToProp' pts ts bt vs bs as
sentToProp' (Sumti Untagged (QAtom q rels (Variable v)):pts) ts bt vs bs as =
	quantified (fromMaybe "su'o" q)
		   (\x -> bigAnd (map (\rel -> relToPred rel bs x) rels))
		   (\x ->
	    sentToProp' pts ts bt vs
	    (Map.insert (Variable v) x bs) as)

selbriToRelClauseBridiTail :: Selbri -> BridiTail
selbriToRelClauseBridiTail (Negated sb) =
    let BridiTail3 sb' tts = selbriToRelClauseBridiTail sb
    in BridiTail3 (Negated sb') tts
selbriToRelClauseBridiTail (TanruUnit tu las) =
    BridiTail3 (TanruUnit tu []) las

selbriToPred :: Selbri -> Bindings -> (Obj -> Prop)
selbriToPred sb bs = relToPred (Restrictive $ Subsentence [] [] bt) bs
    where bt = selbriToRelClauseBridiTail sb

relToPred :: RelClause -> Bindings -> (Obj -> Prop)
relToPred (Restrictive subs) bs = \x -> evalRelClause subs bs x


quantified :: Quantifier -> ( Obj -> Prop ) -> ( Obj -> Prop ) -> Prop
quantified q suchthat inner =
    (case q of {"ro" -> Forall;
	  "su'o" -> Exists}) (\x ->
	      case suchthat x of
		   Not Eet -> inner x
		   _ ->
		      (case q of "ro" -> Impl
				 "su'o" -> And)
			    (suchthat x)
			    (inner x)
	      )
evalRelClause :: Subsentence -> Bindings -> Obj -> Prop
evalRelClause subs bs x =
    sentToProp subs [rv] (Map.insert rv x (shuntVars bs RelVar))
	where rv = RelVar 1

shuntVars :: Bindings -> (Int -> SumtiAtom) -> Bindings
shuntVars bs var = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 0 .. head [ n | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]
