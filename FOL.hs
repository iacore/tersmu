module FOL where 
import Control.Monad.State

data Prop r t c o q
    = Not    (Prop r t c o)
    | Connected Connective (Prop r t c o) (Prop r t c o)
    | NonLogConnected c (Prop r t c o) (Prop r t c o)
    | Quantified q (Maybe (Int -> Prop r t c o)) (Int -> Prop r t c o)
    | Modal o (Prop r t c o)
    | Rel    r [t]
    | Eet

data Connective = And | Or | Impl | Equiv
    deriving (Eq, Ord)
data Quantifier = Exists | Forall | Exactly Int | Gadri String | QuestionQuantifier
    deriving (Eq, Ord)

instance Show Connective where
    show And = "/\\"
    show Or = "\\/"
    show Impl = "-->"
    show Equiv = "<->"

instance Show Quantifier where
    show Exists = "EX"
    show Forall = "FA"
    show (Gadri g) = "{"++g++"}"
    show (Exactly n) = "EQ(" ++ show n ++ ")"
    show QuestionQuantifier = "?"

class Term t where
    var :: Int -> t

class Rel r where
    relstr :: r -> String

-- terpProp: lift an interpretation of atomic formulae, operators, and
-- quantifiers to an interpretation of arbitrary formula
terpProp ::
    (r1 -> [t1] -> Prop r2 t2 c o2 q2)
    -> (o1 -> o2)
    -> (q1 -> q2)
    -> Prop r1 t1 c o1 q1 -> Prop r2 t2 c o2 q2
terpProp terpAtomic terpOp terpQ p = terpProp' p
    where terpProp' (Rel r ts) = terpAtomic r ts
	  terpProp' (Quantified q r p) =
	      Quantified (terpQ q) (case r of
		  Nothing -> Nothing
		  Just r' -> Just (\v -> terpProp' $ r' v))
		      (\v -> terpProp' $ p v)
	  terpProp' (Not p) = Not $ terpProp' p
	  terpProp' (Connected c p1 p2) =
	      Connected c (terpProp' p1) (terpProp' p2)
	  terpProp' (NonLogConnected c p1 p2) =
	      NonLogConnected c (terpProp' p1) (terpProp' p2)
	  terpProp' Eet = Eet
	  terpProp' (Modal o p) = Modal (terpOp o) (terpProp' p)

bigAnd :: [Prop r t c o] -> Prop r t c o
bigAnd ps = bigAnd' $ filter (\p -> case p of {Not Eet -> False; _ -> True}) ps
    where bigAnd' [] = Not Eet
	  bigAnd' [p] = p
	  bigAnd' (p:ps) = Connected And p (bigAnd' ps)

-- instance (Rel r, Term t) => Show (Prop r t) where
--     show p = evalState (serialise p False) 1

-- type PropPrintFlags = Bool -- insert newlines and tabs?

-- serialise :: (Rel r, Term t) => (Prop r t) -> PropPrintFlags -> State Int String
-- serialise p f = _serialise p f 0
-- 
-- _serialise :: (Rel r, Term t) => Prop r t -> PropPrintFlags -> Int -> State Int String
-- _serialise (Not p) f d =
--     do s <- _serialise p f (d+1)
--        return $ "! ( " ++ s ++ " )"
-- _serialise (Connected c p1 p2) f d =
--     do s1 <- _serialise p1 f (d+1); s2 <- _serialise p2 f (d+1);
--        return $ "( " ++ s1 ++ " " ++ show c ++ " " ++
-- 	   (if f then "\n"++(replicate (d+1) '\t') else "") ++ s2 ++ " )" 
-- _serialise (Quantified q r p::Prop r t) f d =
--     do n <- get
--        put $ n+1
--        case r of Nothing -> do s <- _serialise (p n) f (d+1)
-- 			       return $ show q ++ " " ++
-- 				   objlogstr (var n::t) ++
-- 				   ". " ++ s
-- 		 Just r' -> do s1 <- _serialise (r' n) f (d+1)
-- 			       s2 <- _serialise (p n) f (d+1)
-- 			       return $ show q ++ " " ++
-- 				   objlogstr (var n::t) ++ 
-- 				   ":(" ++ s1 ++ ")" ++
-- 				   ". " ++ s2
-- _serialise (Rel r ts) f d =
--     return $ relstr r ++ "(" ++ unwords (map objlogstr ts) ++ ")"
-- _serialise Eet f d = return "_|_"


-- XXX: broken
{-
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
-}
