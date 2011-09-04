module Lojban where

import FOL

import Data.Maybe
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

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
	   | Sumti5 (Maybe Quantifier) [RelClause] SumtiAtom
	   deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Term  -- noi
	       deriving (Eq, Show, Ord)
data SumtiAtom = Constant Obj
	       | Description Gadri Selbri
	       | Variable Int -- da
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       | Assignable Int -- ko'a
	       | Ri -- ri
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
instance SumtiTermType SumtiAtom where term tag x = term tag (Sumti5 Nothing [] x)

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

data PropCxt = PropCxt {bindings::Bindings, implicitVars::[SumtiAtom]} 
		deriving (Eq, Ord, Show)
data Arglist = Arglist {args :: [Obj], position::Int}
		deriving (Eq, Ord, Show)
appendToArglist :: Arglist -> Obj -> Arglist
appendToArglist as@(Arglist os n) o = Arglist (setArg os n o) (n+1)
setArg :: [Obj] -> Int -> Obj -> [Obj]
setArg os n o =
    let (a,b) = splitAt (n-1) os
	in case b of [] -> a++(replicate ((n-1)-(length a)) "zo'e")++[o]
		     (_:bs) -> a++[o]++bs
swapArgs :: [Obj] -> Int -> Int -> [Obj]
swapArgs os n m =
    let lookupArg k = if k <= length os then os!!(k-1) else "zo'e"
	a = lookupArg n
	b = lookupArg m
	in setArg (setArg os m a) n b

emptyPropCxt :: PropCxt
emptyPropCxt = PropCxt Map.empty []
newArglist :: Arglist
newArglist = Arglist [] 1

sentToProp :: Subsentence -> PropCxt -> Prop
sentToProp (Subsentence ps ts bt) pc = sentToProp' ps ts bt pc newArglist

sentToProp' :: [Term] -> [Term] -> BridiTail -> PropCxt -> Arglist -> Prop
--sentToProp' a b c d e | trace ("sentToProp': "
--    ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d ++ " " ++
--	show e ) False = undefined
--
sentToProp' ps ts (ConnectedBT con bt1 bt2) pc as =
    let p1 = sentToProp' ps ts bt1 pc as
	p2 = sentToProp' ps ts bt2 pc as
	in connToFOL con p1 p2

sentToProp' ps ts (BridiTail3 (Negated sb) tts) pc as =
    Not $ sentToProp' ps ts (BridiTail3 sb tts) pc as

sentToProp' [] [] bt (PropCxt bs (v:vs)) as =
    sentToProp' [] [term Untagged v] bt (PropCxt bs vs) as

sentToProp' [] [] (BridiTail3 sb tts) pc as | tts /= [] =
    let as' = if (args as) == [] then (Arglist [] 2) else as
	in sentToProp' [] tts (BridiTail3 sb []) pc as'

sentToProp' [] [] (GekSentence (ConnectedGS con s1 s2 tts)) pc as =
    let p1 = sentToProp'
		(prenex s1) (terms s1) (extendTail (bridiTail s1) tts) pc as
	p2 = sentToProp'
		(prenex s2) (terms s2) (extendTail (bridiTail s2) tts) pc as
	in connToFOL con p1 p2

sentToProp' [] [] (GekSentence (NegatedGS gs)) pc as =
    Not $ sentToProp' [] [] (GekSentence gs) pc as

sentToProp' [] [] (BridiTail3 (TanruUnit tu las) []) pc as =
    case tu of Brivla bv -> Rel bv (args as)
	       Permuted s tu ->
		   let (Arglist os n) = as in
		       sentToProp' [] [] (BridiTail3 (TanruUnit tu las) []) pc
			(Arglist (swapArgs os 1 s) n)

sentToProp' [] (t:ts) bt pc@(PropCxt bs vs) as =
    case t of
	 Negation -> sentToProp' [t] ts bt pc as
	 Sumti tag (ConnectedSumti con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti tag s1):ts) bt pc as
		    p2 = sentToProp' [] ((Sumti tag s2):ts) bt pc as
		    in connToFOL con p1 p2
	 Sumti tag s@(Sumti5 q rels sa) ->
	     case sa of
		  Variable v ->
		      case (Map.lookup (Variable v) bs) of
			   Nothing ->
			       sentToProp' [term Untagged s]
				(term tag (Variable v):ts) bt pc as
			   Just o ->
			       sentToProp' []
				(term tag (Constant o):ts) bt pc as
		  Constant o ->
		      let as' = case tag of Untagged -> as
					    FA n -> as{position=n}
			  as'' = appendToArglist as' o
			  pc' = PropCxt (Map.insert (Ri) o bs) vs
		      in sentToProp' [] ts bt pc' as''
		  rv@(RelVar _) ->
		      let vs' = delete rv vs
			  Just o = (Map.lookup rv bs)
			  in sentToProp' [] 
			      (term tag (Constant o):ts) bt
			      (PropCxt bs vs') as
		  Ri ->
		      let Just o = (Map.lookup Ri bs)
			  in sentToProp' [] 
			      (term tag (Constant o):ts) bt
			      pc as
		  Description g sb ->
		      quantified (fromMaybe "su'o" q)
				 (Restrictive (Subsentence [] []
				    (selbriToRelClauseBridiTail sb)):rels)
				 pc
				 (\x -> sentToProp' []
					  (term tag (Constant x):ts) bt pc as)
			-- TODO: optional xorlo, in some form



sentToProp' (Negation:pts) ts bt pc as =
    Not $ sentToProp' pts ts bt pc as
sentToProp' (Sumti Untagged (Sumti5 q rels (Variable v)):pts) ts bt
	pc@(PropCxt bs vs) as =
	    quantified (fromMaybe "su'o" q) rels pc ( \x ->
		sentToProp' pts ts bt
		(PropCxt (Map.insert (Variable v) x bs) vs) as )

quantified :: Quantifier -> [RelClause] -> PropCxt -> ( Obj -> Prop ) -> Prop
quantified q rels pc inner =
    (case q of {"ro" -> Forall;
	  "su'o" -> Exists}) (\x ->
	      let prependRels :: [RelClause] -> Prop -> Prop 
		  prependRels [] p = p
		  prependRels ((Restrictive subs):rels) p =
		      (case q of "ro" -> Impl
				 "su'o" -> And)
			    (evalRelClause subs pc x)
			    (prependRels rels p)
	       in
		prependRels rels $ inner x
	      )
evalRelClause :: Subsentence -> PropCxt -> Obj -> Prop
evalRelClause subs pc@(PropCxt bs vs) x =
    sentToProp subs (PropCxt (Map.insert rv x bs) (rv:vs))
	where rv = tryUnbound 1
	      tryUnbound n = if isNothing (Map.lookup (RelVar n) bs)
			     then (RelVar n)
			     else tryUnbound (n+1)

selbriToRelClauseBridiTail :: Selbri -> BridiTail
selbriToRelClauseBridiTail (Negated sb) =
    let BridiTail3 sb' tts = selbriToRelClauseBridiTail sb
    in BridiTail3 (Negated sb') tts
selbriToRelClauseBridiTail (TanruUnit tu las) =
    BridiTail3 (TanruUnit tu []) las
