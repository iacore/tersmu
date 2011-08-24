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
type Selbri = String
data Term = Sumti Sumti
	  | Negation
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
	       | RelVar -- ke'a
	       | LambdaVar -- ce'u
	       deriving (Eq, Show, Ord)

data Connective = Connective Bool Char Bool
		deriving (Eq, Show, Ord)
type Brivla = String

type Quantifier = String

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
emptyPropCxt :: PropCxt
emptyPropCxt = PropCxt Map.empty []

sentToProp :: Subsentence -> PropCxt -> Prop
sentToProp (Subsentence ps ts sb) pc = sentToProp' ps ts sb pc []

sentToProp' :: [Term] -> [Term] -> Selbri -> PropCxt -> [Obj] -> Prop
--sentToProp' a b c | trace ("sentToProp': "
--    ++ show a ++ " " ++ show b ++ " " ++ show c) False = undefined
sentToProp' [] [] sb (PropCxt bs vs) as =
       case vs of [] -> Rel sb as
		  (v:vs') -> sentToProp' [] [Sumti (Sumti5 (SumtiAtom v))]
			      sb (PropCxt bs vs') as

sentToProp' [] (t:ts) sb pc@(PropCxt bs vs) as =
    case t of
	 Negation -> sentToProp' [t] ts sb pc as
	 Sumti (Connected con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti s1):ts) sb pc as
		    p2 = sentToProp' [] ((Sumti s2):ts) sb pc as
		    in connToFOL con p1 p2
	 Sumti (Sumti5 sst) ->
	     case sst of
		  Complex q rels (Variable v) ->
		      case (Map.lookup (Variable v) bs) of
			   Nothing ->
			       sentToProp' [t] ((Sumti (Sumti5 (SumtiAtom
					(Variable v)))):ts) sb pc as
			   Just o ->
			       sentToProp' [] ((Sumti (Sumti5 (SumtiAtom
				      (Constant o)))):ts) sb pc as
		  SumtiAtom (Constant o) ->
		      sentToProp' [] ts sb pc (as ++ [o])
		  SumtiAtom (Variable v) ->
		      sentToProp' [] ((Sumti (Sumti5 (Complex Nothing []
				(Variable v)))):ts) sb pc as
		  SumtiAtom RelVar ->
		      let vs' = delete RelVar vs
			  Just o = (Map.lookup RelVar bs)
			  in sentToProp' [] 
			      (Sumti (Sumti5 (SumtiAtom (Constant o))):ts)
			      sb (PropCxt bs vs') as


sentToProp' (Negation:pts) ts sb pc as =
    Not $ sentToProp' pts ts sb pc as
sentToProp' ((Sumti (Sumti5 (SumtiAtom (Variable v)))):pts) ts sb pc as =
    sentToProp'
	((Sumti (Sumti5 (Complex Nothing [] (Variable v)))):pts) ts sb pc as
sentToProp' ((Sumti (Sumti5 (Complex q rels (Variable v)))):pts) ts sb
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
    sentToProp subs (PropCxt (Map.insert RelVar x bs) (RelVar:vs))
