module Lojban where

import FOL hiding (Prop, Term, Connective)
import qualified FOL (Prop, Term, Connective)

import Bindful

import Data.Maybe
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

type Prop = FOL.Prop JboRel JboTerm

data JboTerm = Var Int
	     | Named String
	     | NonAnaph String
	     | ZoheTerm (Maybe (JboTerm -> Prop))

type Individual = Int

type Obj = JboTerm

data JboRel = Tanru JboPred JboRel
	    | AbsPred Abstractor JboPred
	    | AbsProp Abstractor Prop
	    | Moi Quantifier MOICmavo
	    | Among
	    | Brivla String

type Abstractor = String
type MOICmavo = String

instance FOL.Term JboTerm where
    var n = Var n

instance Rel JboRel where
    relstr r = evalBindful $ logshow r

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
	       | SelbriVar -- fake
	       | Description Gadri (Maybe Quantifier) Selbri
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

data Selbri = Negated Selbri
	    | Selbri4 Selbri4
	    deriving (Eq, Show, Ord)

data Selbri4 = SBTanru Selbri4 Selbri4
	     | TanruUnit TanruUnit2 [Term]
	     deriving (Eq, Show, Ord)

data TanruUnit2 = TUBrivla String
		| TUMe Sumti
		| TUAmong -- fake selbri produced by {me ko'a}
		| TUMoi Quantifier String
		| TUAbstraction String Subsentence
	        | TUPermuted Int TanruUnit2
	        deriving (Eq, Show, Ord)

-- term: convenience function to lift a Sumti or SumtiAtom to a term
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

-- extendTail: adds terms to the end of a bridi tail
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
getBinding :: Bindings -> SumtiAtom -> JboTerm
getBinding bs v = fromJust $ Map.lookup v bs

type ImplicitVars = [SumtiAtom]

type JboPred = JboTerm -> Prop

data Arglist = Arglist {args :: [Maybe Obj],
			position::Int,
			implicitvars::ImplicitVars}
appendToArglist :: Arglist -> Obj -> Arglist
appendToArglist as@(Arglist os n _) o = incArg (setArg as n (Just o))
    where incArg as@(Arglist os n vs) = Arglist os (n+1) vs
swapArgs :: Arglist -> Int -> Int -> Arglist
swapArgs as@(Arglist os _ _) n m =
    let lookupArg k = if k <= length os then os!!(k-1) else Nothing
	a = lookupArg n
	b = lookupArg m
    in setArg (setArg as m a) n b
resolveArglist :: Arglist -> Bindings -> [JboTerm]
resolveArglist as@(Arglist os _ vs) bs = resolve os vs []
    where resolve (Just o:os) vs ts = resolve os vs (ts++[o])
	  resolve (Nothing:os) (v:vs) ts =
	      resolve os vs (ts++[getBinding bs v])
	  resolve (Nothing:os) [] ts =
	      resolve os [] (ts++[ZoheTerm Nothing])
	  resolve [] (v:vs) ts = resolve [] vs (ts++[getBinding bs v])
	  resolve [] [] ts = ts
appendZohe :: Arglist -> Arglist
appendZohe as = appendToArglist as $ ZoheTerm Nothing
-- delImplicitVars :: Arglist -> ImplicitVars -> Arglist
-- delImplicitVars as@(Arglist os n vs) delvs = Arglist os n (vs\\delvs)

setArg :: Arglist -> Int -> Maybe Obj -> Arglist
setArg as@(Arglist os _ _) n o =
    let (h,t) = splitAt (n-1) os
	l = ((n-1)-(length h))
    in as{args=(h++replicate l Nothing++[o]++drop 1 t)}


sentToProp :: Subsentence -> ImplicitVars -> Bindings -> Prop
sentToProp (Subsentence ps ts bt) vs bs =
    sentToProp' ps ts bt bs (Arglist [] 1 vs)

sentToProp' :: [Term] -> [Term] -> BridiTail -> Bindings -> Arglist -> Prop
--sentToProp' a b c d e | trace ("sentToProp': "
--    ++ show a ++ " " ++ show b ++ " " ++ show c ++ " " ++ show d ++ " " ++
--	show e ) False = undefined
--

-- yes, bridi negation really does scope over the prenex - see CLL:16.11.14
sentToProp' ps ts (BridiTail3 (Negated sb) tts) bs as =
    Not $ sentToProp' ps ts (BridiTail3 sb tts) bs as

-- while giheks are rather different (see e.g. CLL:14.9.11):
sentToProp' [] [] (ConnectedBT con bt1 bt2) bs as =
    let p1 = sentToProp' [] [] bt1 bs as
	p2 = sentToProp' [] [] bt2 bs as
	in connToFOL con p1 p2

sentToProp' [] [] (BridiTail3 (Selbri4 (TanruUnit (TUMe s) _)) tts) bs as =
    sentToProp' [] []
	(BridiTail3 (Selbri4 (TanruUnit TUAmong [])) (Sumti Untagged s:tts))
	bs as

sentToProp' [] [] (BridiTail3 sb tts) bs as | tts /= [] =
    let as' = case (args as) of [] -> as{position=2}
				_  -> as
	in sentToProp' [] tts (BridiTail3 sb []) bs as'

sentToProp' [] [] (GekSentence (ConnectedGS con s1 s2 tts)) bs as =
    let p1 = sentToProp'
		(prenex s1) (terms s1) (extendTail (bridiTail s1) tts) bs as
	p2 = sentToProp'
		(prenex s2) (terms s2) (extendTail (bridiTail s2) tts) bs as
	in connToFOL con p1 p2

sentToProp' [] [] (GekSentence (NegatedGS gs)) bs as =
    Not $ sentToProp' [] [] (GekSentence gs) bs as

sentToProp' [] [] (BridiTail3 (Selbri4 sb) []) bs as =
    let chopsb (SBTanru seltau tertau) as =
	    let p = selbriToPred (Selbri4 seltau) bs
		(r,as') = chopsb tertau as
	    in (Tanru p r, as')
	chopsb (TanruUnit tu las) as =
	    case tu of
		 TUBrivla bv -> (Brivla bv, as)
		 TUMoi q m -> (Moi q m, as)
		 TUAbstraction a subs ->
		     case a of _ | a `elem` ["ka", "ni"] ->
				     (AbsPred a
				      (let lv = LambdaVar 1
				       in (\o ->
					   sentToProp subs [lv] (Map.insert lv
					       o (shuntVars bs LambdaVar))))
				     , as)
				 | a == "poi'i" ->
				     -- poi'i: an experimental NU, which takes
				     -- ke'a rather than ce'u; {ko'a poi'i
				     -- ke'a broda} means {ko'a broda}.
				     -- http://www.lojban.org/tiki/poi'i
				     (AbsPred a
				      (let rv = RelVar 1
				       in (\o ->
					   sentToProp subs [rv] (Map.insert rv
					       o (shuntVars bs RelVar))))
				     , as)
			         | otherwise -> 
				     (AbsProp a (sentToProp subs [] bs), as)
		 TUAmong -> (Among, as)
		 TUPermuted s tu' ->
			   chopsb (TanruUnit tu' las)
				  (swapArgs as 1 s)
	(r,as') = chopsb sb as
	
    in case r of AbsPred "poi'i" p -> 
			p $ head $ resolveArglist (appendZohe as') bs
		 _ -> Rel r (resolveArglist as' bs)

sentToProp' [] (t:ts) bt bs as =
 let argAppended delvs bs tag o =
	 let as' = case tag of Untagged -> as
			       FA n -> as{position=n}
	     as'' = let vs = implicitvars as'
			f v = case o of
				   Var n ->
				    case getBinding bs v of Var n -> True
							    _ -> False
				   _ -> False
		    in as'{implicitvars = (vs\\(delvs++filter f vs))}
	     as''' = appendToArglist as'' o
	     bs' = Map.insert Ri o bs
	 in sentToProp' [] ts bt bs' as'''
 in case t of
	 Negation -> sentToProp' [t] ts bt bs as
	 Sumti tag (ConnectedSumti con s1 s2) ->
		let p1 = sentToProp' [] ((Sumti tag s1):ts) bt bs as
		    p2 = sentToProp' [] ((Sumti tag s2):ts) bt bs as
		    in connToFOL con p1 p2
	 Sumti tag s@(QAtom q rels sa) ->
	     let
		rrels = [evalRel subs bs | rel@(Restrictive subs) <- rels ]
		irels = [evalRel subs bs | rel@(Incidental subs) <- rels ]
		(p, remainingRels) = case sa of
		  Variable n ->
		      case (Map.lookup (Variable n) bs) of
			   Nothing ->
			       -- export to prenex:
			       (\bs -> sentToProp' [term Untagged s]
				(term tag (Variable n):ts) bt bs as, Nothing)
			   Just o ->
			       (\bs -> argAppended [] bs tag o, Just (irels, o))
		  _ -> -- rest are "plural"
		      let (o,irels',delvs) = case sa of
			     NonAnaphoricProsumti ps -> (NonAnaph ps, irels, [])
			     RelVar _ -> (getBinding bs sa, irels, [sa])
			     LambdaVar _ -> (getBinding bs sa, irels, [sa])
			     SelbriVar -> (getBinding bs sa, irels, [sa])
			     anaph@Ri -> 
				 (getBinding bs anaph, irels, [])
			     anaph@(Assignable _) -> 
				 (getBinding bs anaph, irels, [])
			     Name s -> (Named s, irels, [])
			     Zohe -> (zoheExpr irels, [], [])
			     Description _ innerq sb ->
				 let irels' =
					 if isJust innerq then ((\o ->
					     Rel (Moi (fromJust innerq)
						    "mei") [o]) : irels)
					    else irels
				     irels'' = (selbriToPred sb bs:irels')
				 in (zoheExpr irels'', [], [])
			     where zoheExpr [] = ZoheTerm Nothing
				   zoheExpr irels =
				       ZoheTerm (Just $ andPred irels)
		     in case q of
			 Nothing -> (\bs -> argAppended delvs bs tag o, Just (irels', o))
			 Just q' ->
			     (\bs -> quantified q' (Just $ andPred (isAmong o:rrels))
				     (\o -> argAppended delvs bs tag o),
				 Just (irels', o))
	    in case remainingRels of
		    Nothing -> p bs
		    Just (irels, o) ->
			let bs' = assign bs o rels
			in case irels of [] -> p bs'
					 _ -> Connected And
					    (andPred irels o) (p bs')
	 Sumti tag s@(QSelbri q rels sb) ->
	     let rrels = [evalRel subs bs | rel@(Restrictive subs) <- rels ]
		 irels = [evalRel subs bs | rel@(Incidental subs) <- rels ]
		 p = Just $ andPred (selbriToPred sb bs:rrels)
	     in quantified q p
		    (andPred ((\o -> argAppended [] (assign bs o rels) tag o)
				:irels))
    where assign bs o rels =
	      foldr (\n -> Map.insert (Assignable n) o)
		    bs
		    [n | rel@(Assignment
			(Sumti _ (QAtom _ _ (Assignable n)))) <- rels]
	    
sentToProp' (Negation:pts) ts bt bs as =
    Not $ sentToProp' pts ts bt bs as
sentToProp' (Sumti Untagged (QAtom q rels (Variable n)):pts) ts bt bs as =
	quantified (fromMaybe Exists q)
		   (case rels of [] -> Nothing
				 _  -> Just $ (\o ->
				     let bs' = Map.insert (Variable n) o bs
				     in bigAnd (map (\(Restrictive subs) ->
					 evalRel subs bs' o) rels)))
		   (\o -> sentToProp' pts ts bt
			   (Map.insert (Variable n) o bs) as)

quantified :: Quantifier -> Maybe JboPred -> JboPred -> Prop
quantified q r p = Quantified q (case r of Nothing -> Nothing
				           Just r -> Just $ singpred r)
				(singpred p)
    where singpred p = \v -> p (Var v)

selbriToRelClauseBridiTail :: Selbri -> BridiTail
selbriToRelClauseBridiTail (Negated sb) =
    let BridiTail3 sb' tts = selbriToRelClauseBridiTail sb
    in BridiTail3 (Negated sb') tts
selbriToRelClauseBridiTail (Selbri4 sb) =
    let splitsb4 (SBTanru sb1 sb2) =
	    let (sb2',las) = splitsb4 sb2
	    in (SBTanru sb1 sb2', las)
	splitsb4 (TanruUnit tu las) = (TanruUnit tu [], las)
	(sb', las) = splitsb4 sb
    in BridiTail3 (Selbri4 sb') las

selbriToPred :: Selbri -> Bindings -> JboPred
selbriToPred sb bs = \o ->
    sentToProp (Subsentence [] [term Untagged rv] bt)
	[] (Map.insert rv o bs)
    where bt = selbriToRelClauseBridiTail sb
	  rv = SelbriVar

evalRel :: Subsentence -> Bindings -> JboPred
evalRel subs bs = \o ->
    sentToProp subs [rv] (Map.insert rv o (shuntVars bs RelVar))
	where rv = RelVar 1

shuntVars :: Bindings -> (Int -> SumtiAtom) -> Bindings
shuntVars bs var = foldr ( \n -> Map.insert (var $ n+1)
					    (getBinding bs (var n)) )
			 bs
			 [ 0 .. head [ n | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]


---- Printing routines, in lojban and in (customized) logical notation

class JboShow t where
    jboshow :: t -> Bindful SumtiAtom String
    logshow :: t -> Bindful SumtiAtom String
    logjboshow :: Bool -> t -> Bindful SumtiAtom String

    -- minimal complete definition: (jboshow and logshow) or logjboshow
    jboshow = logjboshow True
    logshow = logjboshow False
    logjboshow jbo = if jbo then jboshow else logshow

withNextVariable f =
    do vals <- getValues
       let n = head [ n | n <- [1..], not $ (Variable n) `elem` vals ]
	   in withBinding (Variable n) f

withShuntedRelVar f =
    do twiddleBound $ \s -> case s of RelVar n -> RelVar $ n+1
				      _ -> s
       r <- withBinding (RelVar 1) f
       twiddleBound $ \s -> case s of RelVar n -> RelVar $ n-1
				      _ -> s
       return r
withShuntedLambda f =
    do twiddleBound $ \s -> case s of LambdaVar n -> LambdaVar $ n+1
				      _ -> s
       r <- withBinding (LambdaVar 1) f
       twiddleBound $ \s -> case s of LambdaVar n -> LambdaVar $ n-1
				      _ -> s
       return r

instance JboShow Quantifier where
    jboshow Exists = return "su'o"
    jboshow Forall = return "ro"
    jboshow (Exactly n) = return $ show n
    logshow = return . show

instance JboShow JboRel where
    logjboshow jbo (Tanru p r) =
	do withShuntedRelVar (\n ->
	       do s <- logjboshow jbo (p (Var n))
		  s' <- logjboshow jbo r
		  return $ if jbo then "poi'i " ++ s ++ " kei " ++ s'
				  else "[" ++ s ++ "] " ++ s' )
    logjboshow jbo (Moi q m) = do s <- logjboshow jbo q
				  return $ s ++ m
    logjboshow jbo (AbsPred a p) =
	do withShuntedLambda (\n ->
	       do s <- logjboshow jbo (p (Var n))
		  return $ if jbo then a ++ " " ++ s ++ " kei" 
				  else a ++ "[" ++ s ++ "]" )
    logjboshow jbo (AbsProp a p) =
	do s <- logjboshow jbo p
	   return $ if jbo then a ++ " " ++ s ++ " kei"
			   else a ++ "[" ++ s ++ "]"
    logjboshow _ Among = return "me"
    logjboshow _ (Brivla s) = return s

isAmong :: JboTerm -> (JboTerm -> Prop)
isAmong y = \o -> Rel Among [o,y]

instance JboShow JboTerm where
    logjboshow _ (ZoheTerm Nothing) = return "zo'e"
    logjboshow jbo (ZoheTerm (Just p)) =
	do withShuntedRelVar (\n ->
	       do s <- logjboshow jbo (p (Var n))
		  return $ if jbo then "zo'e noi " ++ s ++ " ku'o" 
				  else "zo'e:(" ++ s ++ ")" )
    logjboshow jbo (Var n) =
	do v <- binding n 
	   return $ if jbo then case v of
				    Variable 1 -> "da"
				    Variable 2 -> "de"
				    Variable 3 -> "di"
				    Variable n -> "da xi " ++ jbonum n
				    RelVar 1 -> "ke'a"
				    RelVar n -> "ke'a xi " ++ jbonum n
				    LambdaVar 1 -> "ce'u"
				    LambdaVar n -> "ce'u xi " ++ jbonum n
			    else case v of
				    Variable n -> "x" ++ show n
				    RelVar 1 -> "_"
				    RelVar n -> "_" ++ show n
				    LambdaVar n -> "\\" ++ show n
    logjboshow True (Named s) = return $ "la " ++ s ++ "."
    logjboshow False (Named s) = return s
    logjboshow _ (NonAnaph s) = return s
	
jbonum 0 = "no"
jbonum 1 = "pa"
jbonum 2 = "re"
jbonum 3 = "ci"
jbonum 4 = "vo"
jbonum 5 = "mu"
jbonum 6 = "xa"
jbonum 7 = "ze"
jbonum 8 = "bi"
jbonum 9 = "so"

instance JboShow Prop
    where {logjboshow jbo p = liftM (if jbo then unwords else concat)
				$ logjboshow' jbo [] p
	where
	  logjboshow' :: Bool -> [String] -> Prop -> Bindful SumtiAtom [String]
	  logjboshow' jbo ps (Quantified q r p) =
	     withNextVariable (\n ->
	      do qs <- logjboshow jbo q
	         vs <- logjboshow jbo (Var n)
	         rss <- case r of
	      	    Nothing -> return []
	      	    Just r' ->
	      		do ss <- withShuntedRelVar (\m ->
	      			  logjboshow' jbo [] (r' m) )
	      		   return $ [if jbo then "poi" else ":("]
	      			     ++ ss
	      			     ++ [if jbo then "ku'o" else ")"]
	         logjboshow' jbo (ps ++ [qs,vs] ++ rss) (p n) )
	  logjboshow' jbo ps p | ps /= [] =
	      do ss <- logjboshow' jbo [] p
	         return $ ps ++ [if jbo then "zo'u" else ". "] ++ ss
	  logjboshow' jbo ps (Connected c p1 p2) =
	      do ss1 <- logjboshow' jbo ps p1
	         ss2 <- logjboshow' jbo ps p2
	         return $ if jbo then case c of And -> ["ge"]
					        Or -> ["ga"]
					        Impl -> ["ga", "nai"]
					        Equiv -> ["go"]
	      			++ ss1 ++ ["gi"] ++ ss2
	      		   else ["("] ++ ss1 ++
	      		        [" "++show c++" "] ++ ss2 ++ [")"]
	  logjboshow' jbo ps (Not p) =
	      do ss <- logjboshow' jbo ps p
	         return $ (if jbo then ["na","ku"] else ["!"]) ++ ss
	  logjboshow' jbo@True ps (Rel r []) =
	      do s <- jboshow r
	         return [s]
	  logjboshow' True ps (Rel r (x1:xs)) =
	      do s1 <- jboshow x1
	         s2 <- jboshow r
	         ss <- mapM jboshow xs
	         return $ [s1,s2] ++ ss
	  logjboshow' False ps (Rel r ts) =
	      do s <- logshow r
		 tss <- mapM logshow ts
	         return $
	             [s ++ "(" ++ (concat $ intersperse "," tss) ++ ")"]
	  logjboshow' True ps Eet = return ["jitfa"]
	  logjboshow' False ps Eet = return ["_|_"]
	  }

