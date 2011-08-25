module Lojban where

import FOL

import Data.Maybe
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

data Subsentence = Subsentence {prenex::[Term], terms::[Term], selbri::Selbri}
		 deriving (Eq, Show, Ord)

data Term = Sumti Tag Sumti
	  | Negation
	  | SelbriMarker
	  deriving (Eq, Show, Ord)
data Tag = Untagged
	 | FA Int
	 deriving (Eq, Show, Ord)
data Sumti = Connected Connective Sumti Sumti
	   | Sumti5 Sumti5
	   deriving (Eq, Show, Ord)

data Sumti5 = Complex (Maybe Quantifier) [RelClause] SumtiAtom
	    | SumtiAtom SumtiAtom
	    deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       deriving (Eq, Show, Ord)
data SumtiAtom = Constant Obj
	       | Variable Int -- da
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       deriving (Eq, Show, Ord)

data Connective = Connective Bool Char Bool
		deriving (Eq, Show, Ord)

data Selbri = Brivla String
	    | Permuted Int Selbri
	    deriving (Eq, Show, Ord)

type Quantifier = String

class SumtiTermTypeype a where term :: Tag -> a -> Term

instance SumtiTermTypeype Sumti where term tag x = Sumti tag x
instance SumtiTermTypeype Sumti5 where term tag x = term tag (Sumti5 x)
instance SumtiTermTypeype SumtiAtom where term tag x = term tag (SumtiAtom x)

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
sentToProp (Subsentence ps ts sb) pc = sentToProp' ps ts sb pc newArglist

sentToProp' :: [Term] -> [Term] -> Selbri -> PropCxt -> Arglist -> Prop
--sentToProp' a b c d e | trace ("sentToProp': "
--    ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d ++ " " ++
--	show e ) False = undefined
sentToProp' [] [] (Brivla bv) (PropCxt bs []) as = Rel bv (args as)
sentToProp' [] [] (Permuted s sb) pc@(PropCxt bs []) as@(Arglist os n) =
    sentToProp' [] [] sb pc (Arglist (swapArgs os 1 s) n)
sentToProp' [] [] sb (PropCxt bs (v:vs)) as =
    sentToProp' [] [term Untagged v] sb (PropCxt bs vs) as

sentToProp' [] (t:ts) sb pc@(PropCxt bs vs) as =
    case t of
	 Negation -> sentToProp' [t] ts sb pc as
	 SelbriMarker -> let as' = if (args as) == [] then (Arglist [] 2)
						      else as
			    in sentToProp' [] ts sb pc as'
			     
	 Sumti tag (Connected con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti tag s1):ts) sb pc as
		    p2 = sentToProp' [] ((Sumti tag s2):ts) sb pc as
		    in connToFOL con p1 p2
	 Sumti tag (Sumti5 sst) ->
	     case sst of
		  Complex q rels (Variable v) ->
		      case (Map.lookup (Variable v) bs) of
			   Nothing ->
			       sentToProp' [term Untagged sst]
				(term tag (Variable v):ts) sb pc as
			   Just o ->
			       sentToProp' []
				(term tag (Constant o):ts) sb pc as
		  SumtiAtom (Constant o) ->
		      let as' = case tag of Untagged -> as
					    FA n -> as{position=n}
			  as'' = appendToArglist as' o
		      in sentToProp' [] ts sb pc as''
		  SumtiAtom v@(Variable _) ->
		      sentToProp' []
			(term tag (Complex Nothing [] v):ts) sb pc as
		  SumtiAtom rv@(RelVar _) ->
		      let vs' = delete rv vs
			  Just o = (Map.lookup rv bs)
			  in sentToProp' [] 
			      (term tag (Constant o):ts) sb
			      (PropCxt bs vs') as


sentToProp' (Negation:pts) ts sb pc as =
    Not $ sentToProp' pts ts sb pc as
sentToProp' (Sumti Untagged (Sumti5 (SumtiAtom (Variable v))):pts) ts sb pc as =
    sentToProp'
	(term Untagged (Complex Nothing [] (Variable v)):pts) ts sb pc as
sentToProp' (Sumti Untagged (Sumti5 (Complex q rels (Variable v))):pts) ts sb
	pc@(PropCxt bs vs) as =
    (case q of {(Just "ro") -> Forall;
	  (Just "su'o") -> Exists;
	  (Nothing) -> Exists }) (\x ->
	      let prependRels :: [RelClause] -> Prop -> Prop 
		  prependRels [] p = p
		  prependRels ((Restrictive subs):rels) p =
		      (case q of Just "ro" -> Impl
				 Just "su'o" -> And
				 Nothing -> And)
			    (evalRelClause subs pc x)
			    (prependRels rels p)
	       in
		prependRels rels $
		    sentToProp' pts ts sb
			(PropCxt (Map.insert (Variable v) x bs) vs) as
	      )
evalRelClause :: Subsentence -> PropCxt -> Obj -> Prop
evalRelClause subs pc@(PropCxt bs vs) x =
    sentToProp subs (PropCxt (Map.insert rv x bs) (rv:vs))
	where rv = tryUnbound 1
	      tryUnbound n = if isNothing (Map.lookup (RelVar n) bs)
			     then (RelVar n)
			     else tryUnbound (n+1)
