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

pnf :: Prop -> Prop
pnf (Impl p1 p2) = Or (Not (pnf p1)) (pnf p2)
pnf (Equiv p1 p2) = Or (And (Not (pnf p1)) (pnf p2))
		       (And (pnf p1) (Not (pnf p2)))
pnf (Not (And p1 p2)) = Or (Not (pnf p1)) (Not (pnf p2))
pnf (Not (Or p1 p2)) = And (Not (pnf p1)) (Not (pnf p2))
pnf (Not (Not p)) = pnf p
pnf (And (Or p1 p2) p3) = pnf (Or (And p1 p3) (And p2 p3))
pnf (And p1 (Or p2 p3)) = pnf (Or (And p1 p2) (And p1 p3))
pnf (Not (Exists f)) = Forall (\x -> pnf (Not (f x)))
pnf (Not (Forall f)) = Exists (\x -> pnf (Not (f x)))
pnf (And (Exists f) p2) = Exists (\x -> pnf (And (f x) p2))
pnf (Or (Exists f) p2) = Exists (\x -> pnf (Or (f x) p2))
pnf (And (Forall f) p2) = Forall (\x -> pnf (And (f x) p2))
pnf (Or (Forall f) p2) = Forall (\x -> pnf (Or (f x) p2))
pnf (And p1 (Exists f)) = Exists (\x -> pnf (And p1 (f x)))
pnf (Or p1 (Exists f)) = Exists (\x -> pnf (Or p1 (f x)))
pnf (And p1 (Forall f)) = Forall (\x -> pnf (And p1 (f x)))
pnf (Or p1 (Forall f)) = Forall (\x -> pnf (Or p1 (f x)))
pnf (Or p1 p2) = Or (pnf p1) (pnf p2)
pnf (And p1 p2) = And (pnf p1) (pnf p2)
pnf (Forall f) = Forall (\x -> pnf(f x))
pnf (Exists f) = Exists (\x -> pnf(f x))
pnf p@(Rel r os) = p
pnf p@(Not (Rel r os)) = p
pnf Eet = Eet

main :: IO ()
main = do 
    print example
    print ( pnf example )
