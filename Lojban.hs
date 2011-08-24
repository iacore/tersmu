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

data PropCxt = PropCxt {bindings::Bindings, arglist::[Obj],
	implicitVars::[SumtiAtom]} 
emptyPropCxt :: PropCxt
emptyPropCxt = PropCxt {bindings=Map.empty, arglist=[], implicitVars=[]}

sentToProp :: Subsentence -> State PropCxt Prop
sentToProp subs = do PropCxt {bindings=b, implicitVars=vs} <- get
		     return $ evalState (sentToPropArgs (prenex subs)
					    (terms subs) (selbri subs))
				  (PropCxt {bindings = b, arglist = [],
				      implicitVars = vs})
sentToPropArgs :: [Term] -> [Term] -> Selbri -> State PropCxt Prop
--sentToPropArgs a b c | trace ("sentToPropArgs: "
--    ++ show a ++ " " ++ show b ++ " " ++ show c) False = undefined
sentToPropArgs [] [] sb =
    do vs <- gets implicitVars
       case vs of [] -> do os <- gets arglist
			   return $ Rel sb os
		  (v:vs) ->
		      do s <- get
			 put s{implicitVars=vs}
			 sentToPropArgs [] [Sumti (Sumti5 (SumtiAtom v))] sb

sentToPropArgs [] (t:ts) sb =
    do s <- get
       case t of
	    Negation -> sentToPropArgs [t] ts sb
	    Sumti (Connected con s1 s2) ->
		let p1 = evalState (sentToPropArgs [] ((Sumti s1):ts) sb) s
		    p2 = evalState (sentToPropArgs [] ((Sumti s2):ts) sb) s
		    in return $ connToFOL con p1 p2
	    Sumti (Sumti5 sst) ->
		case sst of
		     Complex q rels (Variable v) ->
			 case (Map.lookup (Variable v) (bindings s)) of
			      Nothing -> sentToPropArgs [t]
				  ((Sumti (Sumti5 (SumtiAtom
					(Variable v)))):ts) sb
			      Just o -> sentToPropArgs []
				  ((Sumti (Sumti5 (SumtiAtom
					(Constant o)))):ts) sb
		     SumtiAtom (Constant o) ->
			do put s{arglist = (arglist s)++[o]}
			   sentToPropArgs [] ts sb
		     SumtiAtom (Variable v) ->
			 sentToPropArgs []
			     ((Sumti (Sumti5 (Complex Nothing []
				(Variable v)))):ts) sb
		     SumtiAtom RelVar ->
			 do put s{implicitVars = delete RelVar (implicitVars s)}
			    let Just o = (Map.lookup RelVar (bindings s))
			    sentToPropArgs [] 
				(Sumti (Sumti5 (SumtiAtom (Constant o))):ts) sb


sentToPropArgs (Negation:pts) ts sb =
    liftM Not $ sentToPropArgs pts ts sb
sentToPropArgs ((Sumti (Sumti5 (SumtiAtom (Variable v)))):pts) ts sb =
    sentToPropArgs
	((Sumti (Sumti5 (Complex Nothing [] (Variable v)))):pts) ts sb
sentToPropArgs ((Sumti (Sumti5 (Complex q rels (Variable v)))):pts) ts sb =
    do s <- get
       return $ (case q of {(Just "ro") -> Forall;
			    (Just "su'o") -> Exists;
			    (Nothing) -> Exists }) (\x ->
		let prependRels :: [RelClause] -> Prop -> Prop 
		    prependRels [] p = p
		    prependRels ((Restrictive subs):rels) p =
			(case q of Just "ro" -> Impl
			           Just "su'o" -> And
			           Nothing -> And)
			   ((evalState (evalRelClause subs) s) x)
				      (prependRels rels p)
		    in
		prependRels rels $ let substate = s{bindings=(
				  Map.insert (Variable v) x (bindings s))} in
			evalState (sentToPropArgs pts ts sb) substate 
	      )
evalRelClause :: Subsentence -> State PropCxt (Obj -> Prop)
evalRelClause subs = do pc@(PropCxt {bindings=b, implicitVars=vs}) <- get
			return $ \x -> (
			    let pc' = PropCxt {
				    bindings = (Map.insert RelVar x b),
				    implicitVars = (RelVar:vs),
				    arglist = [] } in
			    evalState (sentToProp subs) pc'
			    )
						 
