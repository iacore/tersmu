module FOL where

import Control.Monad.State

data Prop r t
    = Not    (Prop r t)
    | And    (Prop r t) (Prop r t)
    | Or     (Prop r t) (Prop r t)
    | Impl   (Prop r t) (Prop r t)
    | Equiv  (Prop r t) (Prop r t)
    | Rel    r [t]
    | Forall (t -> (Prop r t))
    | Exists (t -> (Prop r t))
    | Eet

class Term t where
    singvar :: Int -> t
    objlogstr :: t -> String
    objjbostr :: t -> String

class Rel r where
    relstr :: r -> String

instance (Rel r, Term t) => Show (Prop r t) where
    show p = evalState (serialise p True) 1

type PropPrintFlags = Bool -- insert newlines and tabs?

bigAnd :: [Prop r t] -> (Prop r t)
bigAnd [] = Not Eet
bigAnd [p] = p
bigAnd (p:ps) = And p (bigAnd ps)

bigOr :: [Prop r t] -> (Prop r t)
bigOr [] = Eet
bigOr [p] = p
bigOr (p:ps) = Or p (bigOr ps)

serialise :: (Rel r, Term t) => (Prop r t) -> PropPrintFlags -> State Int String
serialise p f = _serialise p f 0

_serialise :: (Rel r, Term t) => (Prop r t) -> PropPrintFlags -> Int -> State Int String
_serialise (Not p) f d	    =
    do
	s <- _serialise p f (d+1)
	return $ "! ( " ++ s ++ " )"
_serialise (And p1 p2) f d  = do {
    s1 <- _serialise p1 f (d+1); s2 <- _serialise p2 f (d+1);
    return $ "( " ++ s1 ++ " /\\ " ++ (if f then "\n"++(replicate (d+1) '\t') else "") ++ s2 ++ " )" }
_serialise (Or p1 p2) f d   = do {
    s1 <- _serialise p1 f (d+1); s2 <- _serialise p2 f (d+1);
    return $ "( " ++ s1 ++ " \\/ " ++ (if f then "\n"++(replicate (d+1) '\t') else "") ++ s2 ++ " )" }
_serialise (Impl p1 p2) f d = do {
    s1 <- _serialise p1 f (d+1); s2 <- _serialise p2 f (d+1);
    return $ "( " ++ s1 ++ " --> " ++ (if f then "\n"++(replicate (d+1) '\t') else "") ++ s2 ++ " )" }
_serialise (Equiv p1 p2) f d = do {
    s1 <- _serialise p1 f (d+1); s2 <- _serialise p2 f (d+1);
    return $ "( " ++ s1 ++ " <-> " ++ (if f then "\n"++(replicate (d+1) '\t') else "") ++ s2 ++ " )" }
_serialise (Rel r ts) f d   = return $ relstr r ++ "(" ++ unwords (map objlogstr ts) ++ ")"
_serialise (Forall q) f d   = do
    n <- get
    put $ n+1
    let v = singvar n in
        do s <- _serialise (q $ v) f (d+1)
           return $ "FA " ++ objlogstr v ++ ". " ++ s
_serialise (Exists q) f d   = do
    n <- get
    put $ n+1
    let v = singvar n in
        do s <- _serialise (q $ v) f (d+1)
           return $ "EX " ++ objlogstr v ++ ". " ++ s
_serialise Eet f d	    = return "_|_"


-- XXX: broken
pnf :: (Prop r t) -> (Prop r t)
pnf (Impl p1 p2) = pnf $ Or (Not p1) p2
pnf (Equiv p1 p2) = pnf $ Or (And (Not p1) p2)
			     (And p1 (Not p2))
pnf (Or p1 p2) =
    pnfOr (pnf p1) (pnf p2)
	where pnfOr (Forall f) p2 = pnf $ Forall (\x -> Or (f x) p2)
	      pnfOr (Exists f) p2 = pnf $ Exists (\x -> Or (f x) p2)
	      pnfOr p1 (Forall f) = pnf $ Forall (\x -> Or p1 (f x))
	      pnfOr p1 (Exists f) = pnf $ Exists (\x -> Or p1 (f x))
	      pnfOr p1 p2 = (Or p1 p2)

pnf (And p1 p2) =
    pnfAnd (pnf p1) (pnf p2)
	where pnfAnd (Forall f) p2 = pnf $ Forall (\x -> And (f x) p2)
	      pnfAnd (Exists f) p2 = pnf $ Exists (\x -> And (f x) p2)
	      pnfAnd p1 (Forall f) = pnf $ Forall (\x -> And p1 (f x))
	      pnfAnd p1 (Exists f) = pnf $ Exists (\x -> And p1 (f x))
	      pnfAnd (Or p3 p4) p2 = pnf $ Or (And p3 p2) (And p4 p2)
	      pnfAnd p1 (Or p3 p4) = pnf $ Or (And p1 p3) (And p1 p4)
	      pnfAnd p1 p2 = (And p1 p2)

pnf (Not p) =
    pnfNot (pnf p)
	where pnfNot (Forall f) = pnf $ Exists (\x -> Not (f x))
	      pnfNot (Exists f) = pnf $ Forall (\x -> Not (f x))
	      pnfNot (And p1 p2) = pnf $ Or (Not p1) (Not p2)
	      pnfNot (Or p1 p2) = pnf $ And (Not p1) (Not p2)
	      pnfNot (Not p) = p
	      pnfNot p = (Not p)

pnf (Forall f) = Forall (\x -> pnf (f x))
pnf (Exists f) = Exists (\x -> pnf (f x))
pnf p = p



propToForeJbo :: (Rel r, Term t) => (Prop r t) -> String
propToForeJbo p = unwords $ propToForeJbo' [] 1 p
    where
    propToForeJbo' :: (Rel r, Term t) => [String] -> Int -> (Prop r t) -> [String]
    propToForeJbo' ps n ((Exists f)::(Prop r t)) =
	propToForeJbo' (ps++["su'o", objjbostr ((singvar n)::t)]) (n+1) (f (singvar n))
    propToForeJbo' ps n ((Forall f)::(Prop r t)) =
	propToForeJbo' (ps++["ro", objjbostr ((singvar n)::t)]) (n+1) (f (singvar n))
    propToForeJbo' ps n p | ps /= [] =
	ps ++ ["zo'u"] ++ (propToForeJbo' [] n p)
    propToForeJbo' ps n (And p1 p2) =
	["ge"] ++ (propToForeJbo' ps n p1) ++ ["gi"] ++ (propToForeJbo' ps n p2)
    propToForeJbo' ps n (Or p1 p2) =
	["ga"] ++ (propToForeJbo' ps n p1) ++ ["gi"] ++ (propToForeJbo' ps n p2)
    propToForeJbo' ps n (Impl p1 p2) =
	["ga", "nai"] ++ (propToForeJbo' ps n p1) ++ ["gi"]
	    ++ (propToForeJbo' ps n p2)
    propToForeJbo' ps n (Equiv p1 p2) =
	["go"] ++ (propToForeJbo' ps n p1) ++ ["gi"] ++ (propToForeJbo' ps n p2)
    propToForeJbo' ps n (Not p) =
	["na","ku"] ++ (propToForeJbo' ps n p)
    propToForeJbo' ps n (Rel r ts) =
	(map objjbostr ts)++[relstr r]
    propToForeJbo' ps n Eet = ["jitfa"]
