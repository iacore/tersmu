module Lojban where

import FOL hiding (Prop, Term, Connective)
import qualified FOL (Prop, Term, Connective)

import Bindful

import Data.Maybe
import Control.Monad.State
import Control.Monad.Cont
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

type Prop = FOL.Prop JboRel JboTerm

data JboTerm = Var Int
	     | Named String
	     | NonAnaph String
	     | UnboundAssignable Int
	     | UnboundLerfuString [Lerfu]
	     | JboQuote [Statement]
	     | Valsi String
	     | ZoheTerm
	     deriving (Eq, Show, Ord)

data JboRel = Tanru JboPred JboRel
	    | AbsPred Abstractor JboPred
	    | AbsProp Abstractor Prop
	    | Moi Quantifier MOICmavo
	    | Among
	    | Brivla String

type JboPred = JboTerm -> Prop

type Abstractor = String
type MOICmavo = String

type Lerfu = Char

instance FOL.Term JboTerm where
    var n = Var n

instance Rel JboRel where
    relstr r = evalBindful $ logshow r


-- Abstract syntax:
data Statement = Statement [Term] Statement1
    deriving (Eq, Show, Ord)

data Statement1 = ConnectedStatement Connective Statement1 Statement1
		| StatementSentence Sentence
		| StatementStatements [Statement]
		deriving (Eq, Show, Ord)

data Subsentence = Subsentence [Term] Sentence
    deriving (Eq, Show, Ord)

data Sentence = Sentence [Term] BridiTail
    deriving (Eq, Show, Ord)

data Term = Sumti Tag Sumti
	  | Negation
	  | Termset [Term]
	  | ConnectedTerms Connective Term Term
	  deriving (Eq, Show, Ord)

data Tag = Untagged
	 | FA Int
	 deriving (Eq, Show, Ord)

data Sumti = ConnectedSumti Connective Sumti Sumti [RelClause]
	   | QAtom (Maybe Quantifier) [RelClause] SumtiAtom
	   | QSelbri Quantifier [RelClause] Selbri
	   deriving (Eq, Show, Ord)

data Connective = Connective Bool Char Bool
		deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Term  -- goi
	       | RestrictiveGOI String Term  -- pe etc.
	       | IncidentalGOI String Term  -- ne etc.
	       deriving (Eq, Show, Ord)

data SumtiAtom = Name String
	       | Variable Int -- da
	       | NonAnaphoricProsumti String -- mi
	       | RelVar Int -- ke'a
	       | LambdaVar Int -- ce'u
	       | SelbriVar -- fake
	       | Description Gadri (Maybe Sumti) (Maybe Quantifier) Selbri [RelClause]
	       | Assignable Int -- ko'a
	       | LerfuString [Lerfu]
	       | Ri -- ri
	       | Quote [Statement]
	       | Word String
	       | Zohe -- zo'e
	       deriving (Eq, Show, Ord)

type Gadri = String

data BridiTail = ConnectedBT Connective BridiTail BridiTail [Term]
	       | BridiTail3 Selbri [Term]
	       | GekSentence GekSentence
	       deriving (Eq, Show, Ord)

data GekSentence = ConnectedGS Connective Subsentence Subsentence [Term]
		 | NegatedGS GekSentence
		 deriving (Eq, Show, Ord)

data Selbri = Negated Selbri
	    | Selbri2 Selbri2
	    deriving (Eq, Show, Ord)

data Selbri2 = SBInverted Selbri3 Selbri2
	     | Selbri3 Selbri3
	     deriving (Eq, Show, Ord)

data Selbri3 = SBTanru Selbri3 Selbri3
	     | ConnectedSB Connective Selbri3 Selbri3
	     | TanruUnit TanruUnit2 [Term]
	     deriving (Eq, Show, Ord)

data TanruUnit2 = TUBrivla String
		| TUMe Sumti
		| TUMoi Quantifier String
		| TUAbstraction String Subsentence
	        | TUPermuted Int TanruUnit2
		| TUSelbri3 Selbri3
	        deriving (Eq, Show, Ord)


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

extendTail :: BridiTail -> [Term] -> BridiTail
extendTail (BridiTail3 sb tts) ts = BridiTail3 sb (tts++ts)
extendTail (ConnectedBT con bt1 bt2 tts) ts =
    ConnectedBT con bt1 bt2 (tts++ts)
extendTail (GekSentence gs) ts =
    GekSentence (extendTailGS gs ts)
	where extendTailGS (ConnectedGS con s1 s2 tts) ts = 
		ConnectedGS con s1 s2 (tts++ts)
	      extendTailGS (NegatedGS gs) ts = NegatedGS (extendTailGS gs ts)

appendRelsToSumti newrels (ConnectedSumti con s1 s2 rels) =
    ConnectedSumti con s1 s2 (rels++newrels)
appendRelsToSumti newrels (QAtom q rels sa) =
    QAtom q (rels++newrels) sa
appendRelsToSumti newrels (QSelbri q rels s) =
    QSelbri q (rels++newrels) s


type Bindings = Map SumtiAtom JboTerm

getBinding :: Bindings -> SumtiAtom -> JboTerm
getBinding bs v =
    case Map.lookup v bs of
      Just o -> o
      Nothing -> case v of
		      (Assignable n) -> UnboundAssignable n
		      (LerfuString s) -> UnboundLerfuString s
		      _ -> error $ show v ++ " not bound.\n"


data Arglist = Arglist {args :: [Maybe JboTerm],
			position::Int,
			implicitvars::ImplicitVars}

type ImplicitVars = [SumtiAtom]

nullArgs vs = Arglist [] 1 vs

appendToArglist :: Arglist -> JboTerm -> Arglist
appendToArglist as@(Arglist os n _) o = incArg (setArg as n (Just o))
    where incArg as@(Arglist os n vs) = Arglist os (n+1) vs
appendZohe :: Arglist -> Arglist
appendZohe as = appendToArglist as ZoheTerm
-- delImplicitVars :: Arglist -> ImplicitVars -> Arglist
-- delImplicitVars as@(Arglist os n vs) delvs = Arglist os n (vs\\delvs)

setArg :: Arglist -> Int -> Maybe JboTerm -> Arglist
setArg as@(Arglist os _ _) n o =
    let (h,t) = splitAt (n-1) os
	l = ((n-1)-(length h))
    in as{args=(h++replicate l Nothing++[o]++drop 1 t)}

swapTerms :: [JboTerm] -> Int -> Int -> [JboTerm]
swapTerms ts n m = take (max (max n m) (length ts)) $
	swap (ts ++ (repeat ZoheTerm)) (n-1) (m-1)

swap :: [a] -> Int -> Int -> [a]
swap as n m = [ if i == n then as!!m else
		if i == m then as!!n else as!!i | i <- [0..] ]
swapFinite as n m = take (length as) $ swap as n m


type StatementMonad = StateT Bindings (Cont Prop)
type SentenceMonad = StateT Arglist (StateT Bindings (Cont Prop))

mapSentM = mapStateT . mapStateT . mapCont
mapSentM2 f m1 m2 = StateT $ \as -> StateT $ \bs -> Cont $ \c ->
    f (runCont (runStateT (runStateT m1 as) bs) c)
      (runCont (runStateT (runStateT m2 as) bs) c)
runStM :: Bindings -> StatementMonad Prop -> Prop
runStM bs m = runCont (runStateT m bs) (\(p,s) -> p)
runSentM :: Arglist -> Bindings -> SentenceMonad Prop -> Prop
runSentM as bs m = runCont (runStateT (runStateT m as) bs) (\((p,_),_) -> p)
getBindings :: SentenceMonad Bindings
getBindings = lift get
putBindings :: Bindings -> SentenceMonad ()
putBindings = lift . put
modifyBindings :: (Bindings -> Bindings) -> SentenceMonad ()
modifyBindings = lift . modify

updateAnaphoraWithJboTerm :: JboTerm -> SentenceMonad ()
updateAnaphoraWithJboTerm o =
    do modifyBindings $ Map.insert Ri o
       case o of Named (c:_) -> modifyBindings $
				   Map.insert (LerfuString [c]) o
		 _ -> return ()

advanceArgPosToBridi :: SentenceMonad ()
advanceArgPosToBridi =
   modify $ \as -> case (args as) of [] -> as{position=2}
				     _  -> as

resolveArglist :: SentenceMonad [JboTerm]
resolveArglist =
    do as@(Arglist os _ vs) <- get
       bs <- getBindings
       let resolve (Just o:os) vs ts = resolve os vs (ts++[o])
	   resolve (Nothing:os) (v:vs) ts =
	       resolve os vs (ts++[getBinding bs v])
	   resolve (Nothing:os) [] ts =
	       resolve os [] (ts++[ZoheTerm])
	   resolve [] (v:vs) ts = resolve [] vs (ts++[getBinding bs v])
	   resolve [] [] ts = ts
       return $ resolve os vs []

stripZohe :: [JboTerm] -> [JboTerm]
stripZohe = reverse . stripZohe' . reverse
    where stripZohe' (ZoheTerm:ts) = ts
	  stripZohe' ts = ts

statementsToProp :: [Statement] -> StatementMonad Prop
statementsToProp ss = sequence (map statementToProp ss) >>= return . bigAnd

statementToProp :: Statement -> StatementMonad Prop
statementToProp (Statement ps s) = prenexed ps $ statement1ToProp s

statement1ToProp :: Statement1 -> StatementMonad Prop
statement1ToProp (ConnectedStatement con s1 s2) =
    do p1 <- statement1ToProp s1
       p2 <- statement1ToProp s2
       return $ connToFOL con p1 p2
statement1ToProp (StatementStatements ss) =
    statementsToProp ss
statement1ToProp (StatementSentence s) =
    evalSentence s []

prenexed :: [Term] -> StatementMonad Prop -> StatementMonad Prop
prenexed ts m =
    do bs <- get
       return $ runStM bs $ prenexed' ts m
    where
	prenexed' [] m = m
	prenexed' (t:ts) m =
	    do p <- evalStateT (handlePrenexTerm t) (nullArgs [])
	       p' <- prenexed ts m
	       return $ bigAnd [p,p']
	handlePrenexTerm t = handleTerm t drop append
        drop = return $ Not Eet
        append _ _ o = do updateAnaphoraWithJboTerm o
			  return $ Not Eet

subsentToProp :: Subsentence -> ImplicitVars -> Bindings -> Prop
subsentToProp (Subsentence ps s) vs bs =
    runStM bs $ prenexed ps $ evalSentence s vs

evalSentence :: Sentence -> ImplicitVars -> StatementMonad Prop
evalSentence (Sentence ts bt) vs =
    evalStateT (sentToProp ts bt) (nullArgs vs)


data JboRels = ConnectedRels Connective JboRels JboRels
	     | JboRel JboRel [Term] ([JboTerm] -> [JboTerm])

sentToProp :: [Term] -> BridiTail -> SentenceMonad Prop

sentToProp (t:ts) bt =
    handleSentenceTerm t $ sentToProp ts bt

sentToProp [] (GekSentence (ConnectedGS con
	(Subsentence pr1 (Sentence ts1 bt1))
	(Subsentence pr2 (Sentence ts2 bt2)) tts)) =
    do bs <- getBindings
       let p1 = subsentToProp
		    (Subsentence pr1 (Sentence ts1 (extendTail bt1 tts)))
		    [] bs
	   p2 = subsentToProp
		    (Subsentence pr2 (Sentence ts2 (extendTail bt2 tts)))
		    [] bs
       return $ connToFOL con p1 p2

sentToProp [] (GekSentence (NegatedGS gs)) =
    do p <- sentToProp [] (GekSentence gs)
       return $ Not p

sentToProp [] (ConnectedBT con bt1 bt2 tts) =
    do as <- get
       p1 <- sentToProp [] (extendTail bt1 tts)
       put as
       p2 <- sentToProp [] (extendTail bt2 tts)
       return $ connToFOL con p1 p2

sentToProp [] (BridiTail3 (Negated sb) tts) =
    do p <- sentToProp [] (BridiTail3 sb tts)
       return $ Not p

sentToProp [] (BridiTail3 (Selbri2 sb@(SBInverted _ _)) tts) =
    sentToProp [] (BridiTail3 (Selbri2 (Selbri3 (uninvert sb))) [])
	where uninvert (SBInverted sb1 (Selbri3 sb2)) = SBTanru (TanruUnit (TUSelbri3 sb2) tts) sb1
	      uninvert (SBInverted sb1 sb2@(SBInverted _ _)) = SBTanru (uninvert sb2) sb1

sentToProp [] (BridiTail3 sb tts) | tts /= [] =
    do advanceArgPosToBridi
       sentToProp tts (BridiTail3 sb [])

sentToProp [] (BridiTail3 (Selbri2 (Selbri3 sb)) []) =
    do bs <- getBindings
       let sb3ToJboRels (SBTanru seltau tertau) extralas =
	       let p = selbriToPred (Selbri2 (Selbri3 seltau)) bs
	       in tanruise p (sb3ToJboRels tertau extralas)
	   sb3ToJboRels (ConnectedSB con sb1 sb2) extralas =
	       ConnectedRels con (sb3ToJboRels sb1 extralas)
				 (sb3ToJboRels sb2 extralas)
	   sb3ToJboRels (TanruUnit tu las1) extralas =
	    let las = las1++extralas
	    in case tu of
		 TUBrivla bv -> JboRel (Brivla bv) las id
		 TUMoi q m -> JboRel (Moi q m) las id
		 TUAbstraction a subs ->
		   case a of
		     "poi'i" ->
			 -- poi'i: an experimental NU, which takes ke'a rather
			 -- than ce'u; {ko'a poi'i ke'a broda} means
			 -- {ko'a broda}. See http://www.lojban.org/tiki/poi'i
			 JboRel (AbsPred a
			  (let rv = RelVar 1
			   in (\o -> subsentToProp subs [rv] (Map.insert rv o
				   (shuntVars bs RelVar)))))
			   las id
		     _ | a `elem` ["ka", "ni"] ->
			 JboRel (AbsPred a
			  (let lv = LambdaVar 1
			   in (\o -> subsentToProp subs [lv] (Map.insert lv o
				   (shuntVars bs LambdaVar)))))
			   las id
		       | otherwise -> 
			 JboRel (AbsProp a (subsentToProp subs [] bs)) las id
		 TUMe s -> JboRel Among (Sumti Untagged s:las) id
		 TUPermuted s tu' ->
			   permute 1 s (sb3ToJboRels (TanruUnit tu' las) [])
		 TUSelbri3 sb -> sb3ToJboRels sb las
	   tanruise p (JboRel r las perm) = JboRel (Tanru p r) las perm
	   tanruise p (ConnectedRels con r1 r2) =
	       ConnectedRels con (tanruise p r1) (tanruise p r2)
	   permute a b (JboRel r las perm) = JboRel r las (\ts -> swapTerms (perm ts) a b)
	   permute a b (ConnectedRels con r1 r2) =
	       ConnectedRels con (permute a b r1) (permute a b r2)
	   evaljborels (JboRel r (la:las) perm) =
	       do advanceArgPosToBridi
		  handleSentenceTerm la $ evaljborels (JboRel r las perm)
	   evaljborels (JboRel (AbsPred "poi'i" p) [] perm) =
	       do ts <- resolveArglist
		  return $ p $ head $ (perm ts) ++ [ZoheTerm]
	   evaljborels (JboRel r [] perm) =
	       do ts <- resolveArglist
		  return $ Rel r (stripZohe (perm ts))
	   evaljborels (ConnectedRels con r1 r2) =
	       do as <- get
		  p1 <- evaljborels r1
		  put as
		  p2 <- evaljborels r2
		  return $ connToFOL con p1 p2
       evaljborels (sb3ToJboRels sb [])

handleSentenceTerm t m =
 let drop = m
     append delvs tag o =
      do bs <- getBindings
         modify $ \as -> case tag of
        	     Untagged -> as
        	     FA n -> as{position=n}
	 modify $ \as ->
	     let vs  = implicitvars as
		 f v = case o of Var n -> case getBinding bs v of
						    Var m -> n==m
						    _     -> False
				 _ -> False
	     in as{implicitvars = (vs\\(delvs++filter f vs))}
	 modify $ \as -> appendToArglist as o
	 updateAnaphoraWithJboTerm o
	 m
 in handleTerm t drop append
 
handleTerm :: (Term -> SentenceMonad Prop ->
	([SumtiAtom] -> Tag -> JboTerm -> SentenceMonad Prop) ->
	SentenceMonad Prop)
handleTerm t drop append =
    do bs <- getBindings
       let assign o rels bs' =
	     -- goi assignment. TODO: proper pattern-matching semantics
	     foldr (\sa -> Map.insert sa o)
		    bs'
		    ([sa | rel@(Assignment
			(Sumti _ (QAtom _ _ sa@(Assignable _)))) <- rels] ++
		    [sa | rel@(Assignment
			(Sumti _ (QAtom _ _ sa@(LerfuString _)))) <- rels])
	   replace t' = handleTerm t' drop append
	   quantifyAtPrenex q r p =
	       -- Unfortunately necessary unmonadic ugliness: the
	       -- effect is to lift the quantification to the prenex,
	       -- as if we'd just used mapSentM (which we can't):
	       StateT $ \as -> StateT $ \bs -> Cont $ \c ->
		   quantified q r (\o -> runCont (runStateT (runStateT (p o) as) bs) c)
	   withRestrictives :: [RelClause] -> ([JboPred] -> SentenceMonad Prop) -> SentenceMonad Prop
	   withRestrictives rels f =
	     withRestrictives' rels [] f
	     where withRestrictives' [] ps f = f ps
		   withRestrictives' (Restrictive subs:rels) ps f =
		       do bs <- getBindings
			  withRestrictives' rels (evalRel subs bs:ps) f
		   withRestrictives' (RestrictiveGOI gstr t:rels) ps f =
		       handleTerm t dropInner appendInner
		    where
		      dropInner = withRestrictives' rels ps f
		      appendInner _ _ io = withRestrictives' rels
			    ((\o -> Rel sb [io,o]):ps) f
		      sb = case gstr of
			    "pe" -> Brivla "srana"
			    "po'u" -> Brivla "du"
			    -- XXX: following are rather approximate... the
			    -- BPFK subordinators section suggests more
			    -- complicated expressions
			    "po'e" -> Tanru (\o -> Rel (Brivla "jinzi") [o])
					(Brivla "srana")
			    "po" -> Tanru (\o -> Rel (Brivla "steci") [o])
					(Brivla "srana")
		   withRestrictives' (rel:rels) ps f =
		       withRestrictives' rels ps f
	   withIncidentals :: [RelClause] -> ([JboPred] -> SentenceMonad Prop) -> SentenceMonad Prop
	   withIncidentals rels f =
	     withIncidentals' rels [] f
	     where withIncidentals' [] ps f = f ps
		   withIncidentals' (Incidental subs:rels) ps f =
		       do bs <- getBindings
			  withIncidentals' rels (evalRel subs bs:ps) f
		   withIncidentals' (IncidentalGOI gstr t:rels) ps f =
		       handleTerm t dropInner appendInner
		    where
		      dropInner = withIncidentals' rels ps f
		      appendInner _ _ io = withIncidentals' rels
			    ((\o -> Rel sb [io,o]):ps) f
		      sb = case gstr of "ne" -> Brivla "srana"
					"no'u" -> Brivla "du"
		   withIncidentals' (rel:rels) ps f =
		       withIncidentals' rels ps f
			   
       case t of
	 Negation -> mapSentM Not drop
	 Sumti tag (ConnectedSumti con s1 s2 rels) ->
	     -- sumti connectives are, in effect, raised to the prenex - i.e.
	     -- treated parallel to unbound variables
	     mapSentM2 (connToFOL con)
		(replace $ Sumti tag $ appendRelsToSumti rels s1)
		(replace $ Sumti tag $ appendRelsToSumti rels s2)
	 ConnectedTerms con t1 t2 ->
	     mapSentM2 (connToFOL con) (replace t1) (replace t2)
	 Termset (t:ts) -> do replace t
			      replace $ Termset ts
	 Termset [] -> drop
	 Sumti tag s@(QAtom q rels sa) ->
	     do let
		 doRels o m = doGivenRels rels o m
		 doGivenRels rels o m =
		     withIncidentals rels $ \ips ->
			do modifyBindings $ assign o rels
			   p <- m
			   return $ bigAnd (p : map ($o) ips)
		 doQuant q o f =
		     case q of Nothing -> f o
			       Just q' -> withRestrictives rels $ \rps ->
				   quantifyAtPrenex q' (Just $ andPred (isAmong o:rps)) f
	        case sa of
		  Variable n ->
		    case (Map.lookup (Variable n) bs) of
		     Nothing ->
			 withRestrictives rels $ \rps ->
			 quantifyAtPrenex (fromMaybe Exists q)
			  (case rps of
			    [] -> Nothing
			    _ -> Just $ andPred rps)
			  (\o -> do modifyBindings $ Map.insert (Variable n) o
				    replace $ Sumti tag (QAtom Nothing rels (Variable n)))
		     Just o -> doRels o $ append [] tag o
		  Description gadri mis miq sb innerRels ->
		      let innerRels' = innerRels ++
			      case mis of Nothing -> []
					  Just is -> [RestrictiveGOI "pe" (Sumti Untagged is)]
		      in withRestrictives innerRels' $ \irps ->
			  do bs <- getBindings
			     let r = andPred $
				   (case miq of
				     Just iq -> [(\o -> Rel (Moi iq "mei") [o])]
				     _ -> []) ++
				   irps ++
				   [selbriToPred sb bs]
			     quantifyAtPrenex (Gadri gadri) (Just r)
				    (\o -> doGivenRels innerRels o $ doQuant q o $
					    (\o' -> doRels o' $ append [] tag o'))
		  _ ->
		      let (o,delvs) = case sa of
			     RelVar _ -> (getBinding bs sa, [sa])
			     LambdaVar _ -> (getBinding bs sa, [sa])
			     SelbriVar -> (getBinding bs sa, [sa])
			     anaph@Ri -> 
				 (getBinding bs anaph, [])
			     anaph@(Assignable _) -> 
				 (getBinding bs anaph, [])
			     anaph@(LerfuString _) -> 
				 (getBinding bs anaph, [])
			     NonAnaphoricProsumti ps -> (NonAnaph ps, [])
			     Name s -> (Named s, [])
			     Zohe -> (ZoheTerm, [])
			     Quote t -> (JboQuote t, [])
			     Word s -> (Valsi s, [])
		      in doRels o $ doQuant q o $ append delvs tag
	 Sumti tag s@(QSelbri q rels sb) ->
	     withRestrictives rels $ \rps ->
	     withIncidentals rels $ \ips ->
	     do bs <- getBindings
		let r = Just $ andPred (selbriToPred sb bs:rps)
		quantifyAtPrenex q r
		     (\o -> do modifyBindings $ assign o rels
			       p <- append [] tag o
			       return $ bigAnd (p : map ($o) ips))
	    

quantified :: Quantifier -> Maybe JboPred -> JboPred -> Prop
quantified q r p = Quantified q (case r of Nothing -> Nothing
				           Just r -> Just $ singpred r)
				(singpred p)
    where singpred p = \v -> p (Var v)

selbriToPred :: Selbri -> Bindings -> JboPred
selbriToPred sb bs = \o ->
    subsentToProp (Subsentence [] (Sentence [] bt))
	[rv] (Map.insert rv o bs)
    where bt = BridiTail3 sb []
	  rv = SelbriVar

evalRel :: Subsentence -> Bindings -> JboPred
evalRel subs bs = \o ->
    subsentToProp subs [rv] (Map.insert rv o (shuntVars bs RelVar))
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

withNextAssignable f =
    do vals <- getValues
       let n = head [ n | n <- [1..], not $ (Assignable n) `elem` vals ]
	   in withBinding (Assignable n) f


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

logjboshowpred jbo p = withShuntedRelVar (\n ->
   if not jbo
     then logjboshow jbo (p n)
     else case p n of
	   Rel sb ts | isJust $ elemIndex (Var n) ts ->
	       do s <- logjboshow jbo sb
		  let i = 1 + fromJust (elemIndex (Var n) ts)
		      ts' = takeWhile (/= ZoheTerm) $ tail $
				case i of 1 -> ts
					  _ -> swapFinite ts 0 (i-1)
		      s' = case i of 1 -> s
				     _ -> seToStr i ++ " " ++ s
		  case ts' of
		    [] -> return s'
		    _ ->
		      do tss <- sequence $ map (logjboshow jbo) ts'
			 return $ s' ++ " be " ++
			      concat (intersperse " bei " tss)
	   _ -> do s <- logjboshow jbo (p n)
		   return $ "poi'i " ++ s ++ " kei" )

instance JboShow JboRel where
    logjboshow jbo (Tanru p r) =
      do rstr <- logjboshow jbo r
	 pstr <- logjboshowpred jbo (\n -> p (Var n))
	 if jbo
	    then return $ "ke " ++ pstr ++ " " ++ rstr ++ " ke'e"
	    else return $ "<" ++ pstr ++ "><" ++ rstr ++ ">"

    logjboshow jbo (Moi q m) = do s <- logjboshow jbo q
				  return $ s ++ " " ++ m
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
    logjboshow False (ZoheTerm) = return " "
    logjboshow True (ZoheTerm) = return "zo'e"
    logjboshow jbo (Var n) =
	do v <- binding n 
	   return $ if jbo then case v of
				    Variable n | n <= 3 -> "d" ++ vowelnum n
				    Variable n -> "da xi " ++ jbonum n
				    RelVar 1 -> "ke'a"
				    RelVar n -> "ke'a xi " ++ jbonum n
				    LambdaVar 1 -> "ce'u"
				    LambdaVar n -> "ce'u xi " ++ jbonum n
				    Assignable n | n <= 5 -> "ko'" ++ vowelnum n
				    Assignable n | n <= 10 -> "fo'" ++ vowelnum (n-5)
				    Assignable n -> "ko'a xi " ++ jbonum n
			    else case v of
				    Variable n -> "x" ++ show n
				    RelVar 1 -> "_"
				    RelVar n -> "_" ++ show n
				    LambdaVar n -> "\\" ++ show n
    logjboshow True (Named s) = return $ "la " ++ s ++ "."
    logjboshow False (Named s) = return s
    logjboshow True (JboQuote ss) = return $ "lu li'o li'u"
    logjboshow False (JboQuote ss) = return $ "\"...\""
    logjboshow True (Valsi s) = return $ "zo " ++ s
    logjboshow False (Valsi s) = return $ "{" ++ s ++ "}"
    logjboshow _ (UnboundAssignable n) = return $
	case n of _ | n <= 5 -> "ko'" ++ vowelnum n
	          _ | n <= 10 -> "fo'" ++ vowelnum (n-5)
		  _ -> "ko'a xi " ++ jbonum n
    logjboshow _ (UnboundLerfuString s) = return $ concat $ intersperse " " $
	map (\c -> case c of _ | c `elem` "aoeui" -> (c:"bu")
			     'y' -> "y bu"
			     _ -> (c:"y")) s
    logjboshow _ (NonAnaph s) = return s
	

vowelnum 1 = "a"
vowelnum 2 = "e"
vowelnum 3 = "i"
vowelnum 4 = "o"
vowelnum 5 = "u"
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
jbonum n = jbonum (n `div` 10) ++ jbonum (n `mod` 10)

seToStr 2 = "se"
seToStr 3 = "te"
seToStr 4 = "ve"
seToStr 5 = "xe"
seToStr n = "se xi " ++ jbonum n

instance JboShow Prop
    where {logjboshow jbo p = liftM (if jbo then unwords else concat)
				$ logjboshow' jbo [] p
	where
	  logjboshow' :: Bool -> [String] -> Prop -> Bindful SumtiAtom [String]
	  logjboshow' True ps (Quantified (Gadri gadri) r p) =
	      withNextAssignable $ \n ->
		  do vs <- logjboshow jbo (Var n)
		     rss <- logjboshowpred jbo (fromJust r)
		     logjboshow' jbo (ps ++ [gadri] ++ [rss] ++
			 ["ku","goi",vs]) (p n)
	  logjboshow' jbo ps (Quantified q r p) =
	      withNextVariable $ \n ->
		  do qs <- logjboshow jbo q
		     vs <- logjboshow jbo (Var n)
		     rss <- case r of
			Nothing -> return $ if jbo then [] else [". "]
			Just r' ->
			 do ss <- withShuntedRelVar (\m ->
				  logjboshow' jbo [] (r' m) )
			    return $ [if jbo then "poi" else ":("]
				     ++ ss
				     ++ [if jbo then "ku'o" else "). "]
		     logjboshow' jbo (ps ++
			 [qs, (if jbo then "" else " ") ++ vs] ++ rss) (p n)
	  logjboshow' jbo ps p | ps /= [] =
	      do ss <- logjboshow' jbo [] p
	         return $ ps ++ [if jbo then "zo'u" else ""] ++ ss
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
	  logjboshow' True ps Eet = return ["jitfa to SPOFU toi"]
	  logjboshow' False ps Eet = return ["_|_ (BUG)"]
	  }
