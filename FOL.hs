module FOL where

import Control.Monad.State

data Prop
    = Not   Prop
    | And   Prop Prop
    | Or    Prop Prop
    | Impl  Prop Prop
    | Equiv  Prop Prop
    | Rel   Rel [Obj]
    | Forall (Obj -> Prop)
    | Exists (Obj -> Prop)
    | Eet

type Rel = String

type Obj = String

-- example = Forall (\x -> Impl (Rel "xirma" [x, "aflingre"]) (Rel "danlu" [x]) )
example = Forall (\x -> Or
        (Exists (\y -> And (Rel "blanu" [y]) (Rel "ponse" [x, y])))
        (Forall (\y -> Impl (Rel "blanu" [y]) (Not (Rel "ponse" [x, y])))))

instance Show Prop where
    show p = evalState (serialise p True) 1

type PropPrintFlags = Bool -- insert newlines and tabs?

bigAnd :: [Prop] -> Prop
bigAnd [] = Not Eet
bigAnd [p] = p
bigAnd (p:ps) = And p (bigAnd ps)

bigOr :: [Prop] -> Prop
bigOr [] = Eet
bigOr [p] = p
bigOr (p:ps) = Or p (bigOr ps)

serialise :: Prop -> PropPrintFlags -> State Integer String
serialise p f = _serialise p f 0

_serialise :: Prop -> PropPrintFlags -> Int -> State Integer String
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
_serialise (Rel r os) f d   = return $ r ++ "(" ++ unwords os ++ ")"
_serialise (Forall q) f d   = do
    n <- get
    put $ n+1
    let v = "x" ++ show n in
        do s <- _serialise (q $ v) f (d+1)
           return $ "FA " ++ v ++ ". " ++ s
_serialise (Exists q) f d   = do
    n <- get
    put $ n+1
    let v = "x" ++ show n in
        do s <- _serialise (q $ v) f (d+1)
           return $ "EX " ++ v ++ ". " ++ s
_serialise Eet f d	    = return "_|_"


-- XXX: broken
pnf :: Prop -> Prop
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



propToForeJbo :: Prop -> String
propToForeJbo p = unwords $ propToForeJbo' [] 1 p
    where
    propToForeJbo' ps n (Exists f) =
	propToForeJbo' (ps++["su'o", da n]) (n+1) (f (da n))
    propToForeJbo' ps n (Forall f) =
	propToForeJbo' (ps++["ro", da n]) (n+1) (f (da n))
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
    propToForeJbo' ps n (Rel r os) =
	os++[r]
    propToForeJbo' ps n Eet = ["jitfa"]
    da 1 = "da"
    da 2 = "de"
    da 3 = "di"
    da 4 = "da xi vo"
    da 5 = "da xi mu"
    da 6 = "da xi xa"

main :: IO ()
main = do 
    print example
    print ( pnf example )
