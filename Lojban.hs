module Lojban where

import FOL hiding (Prop, Term, Connective)
import qualified FOL (Prop, Term, Connective)

import Bindful

import Data.Maybe
import Control.Monad.State
import Control.Monad.Cont
import Control.Applicative
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

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

data JboRel = ConnectedRels Connective JboRel JboRel
	    | PermutedRel Int JboRel
	    | Tanru JboPred JboRel
	    | AbsPred Abstractor JboPred
	    | AbsProp Abstractor Prop
	    | Moi Quantifier MOICmavo
	    | Among JboTerm
	    | Brivla String

type JboPred = JboTerm -> Prop

type Abstractor = String
type MOICmavo = String

type Lerfu = Char

instance FOL.Term JboTerm where
    var n = Var n

instance Rel JboRel where
    relstr r = evalBindful $ logshow r

-- subTerm s t p: replace instances of s with t in p
subTerm :: JboTerm -> JboTerm -> Prop -> Prop
subTerm s t = terpProp $ \r -> \ts -> Rel (subTermInRel s t r) $ map (\x -> if x==s then t else x) ts
subTermInRel t t' (Tanru p r) = Tanru (\o -> subTerm t t' (p o)) (subTermInRel t t' r)
subTermInRel t t' (AbsPred a p) = AbsPred a (\o -> subTerm t t' (p o))
subTermInRel t t' (AbsProp a p) = AbsProp a (subTerm t t' p)
subTermInRel _ _ r = r

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
	 | BAI String
	 deriving (Eq, Show, Ord)

data Sumti = ConnectedSumti Connective Sumti Sumti [RelClause]
	   | QAtom (Maybe Quantifier) [RelClause] SumtiAtom
	   | QSelbri Quantifier [RelClause] Selbri
	   deriving (Eq, Show, Ord)

data Connective = Connective Bool Char Bool
		deriving (Eq, Show, Ord)

data RelClause = Restrictive Subsentence  -- poi
	       | Incidental Subsentence  -- noi
	       | Assignment Sumti  -- goi
	       | RestrictiveGOI String Sumti  -- pe etc.
	       | IncidentalGOI String Sumti  -- ne etc.
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
type VarBindings = Map SumtiAtom JboTerm

getBinding :: Bindings -> SumtiAtom -> JboTerm
getBinding bs v =
    case Map.lookup v bs of
      Just o -> o
      Nothing -> case v of
		      (Assignable n) -> UnboundAssignable n
		      (LerfuString s) -> UnboundLerfuString s
		      _ -> error $ show v ++ " not bound.\n"


data ArgPos = NPos Int | JaiPos | BaiPos String
    deriving (Eq, Show, Ord)
type Args = Map ArgPos JboTerm

nullArgs = Map.empty

joinArgs :: Args -> Args -> Args
joinArgs = Map.union

swapArgs :: ArgPos -> ArgPos -> Args -> Args
swapArgs p1 p2 = Map.mapKeys (\p -> if p == p1 then p2 else if p == p2 then p1 else p)

setArg :: ArgPos -> JboTerm -> Args -> Args
setArg = Map.insert

data Arglist = Arglist {args :: Args, position::Int}
nullArglist = Arglist Map.empty 1

appendToArglist :: JboTerm -> Arglist -> Arglist
appendToArglist o (Arglist as n) = Arglist (Map.insert (NPos n) o as) (n+1)

argsToJboterms :: Args -> [JboTerm]
argsToJboterms as = map (\n -> Map.findWithDefault ZoheTerm (NPos n) as) [1..max] where
    max = maximum $ 1:[n | NPos n <- Map.keys as]


data Arg = Arg Tag JboTerm
addArg :: Arg -> BridiM ()
addArg arg@(Arg tag o) = modifyArglist $
	(appendToArglist o) .
	(\as -> case tag of
	    Untagged -> as
	    FA n -> as{position=n})

-- | addImplicit: adds a jboterm at first empty positional slot
addImplicit :: JboTerm -> BridiM ()
addImplicit o = modifyArglist $ \al ->
    let as = args al
	gap = head $ [1..] \\ [n | NPos n <- Map.keys as]
    in al{args=(Map.insert (NPos gap) o as)}


swapTerms :: [JboTerm] -> Int -> Int -> [JboTerm]
swapTerms ts n m = take (max (max n m) (length ts)) $
	swap (ts ++ (repeat ZoheTerm)) (n-1) (m-1)

swap :: [a] -> Int -> Int -> [a]
swap as n m = [ if i == n then as!!m else
		if i == m then as!!n else as!!i | i <- [0..] ]
swapFinite as n m = take (length as) $ swap as n m


class (Monad m,Applicative m) => Sumbastiful m where
    getSumbastiBindings :: m Bindings
    putSumbastiBindings :: Bindings -> m ()
    setSumbasti :: SumtiAtom -> JboTerm -> m ()
    setSumbasti a t = (Map.insert a t <$> getSumbastiBindings) >>= putSumbastiBindings
    getSumbasti :: SumtiAtom -> m JboTerm
    getSumbasti a = (`getBinding` a) <$> getSumbastiBindings

class (Monad m,Applicative m) => Varpool m where
    getNextFresh :: m Int
    putNextFresh :: Int -> m ()
    getReferenced :: m (Set Int)
    putReferenced :: Set Int -> m ()

    getFreshVar :: m JboTerm
    -- note: crucial that we don't reuse variables, so we can catch "donkey
    -- sentences" which involve scope-breaking sumbasti references to unbound
    -- variables (e.g. {ro cange poi ponse su'o xasli cu darxi ri}).
    getFreshVar = do
	n <- getNextFresh
	putNextFresh $ n+1
	return $ Var n
    setReferenced :: Int -> m ()
    setReferenced n = getReferenced >>= putReferenced . Set.insert n
    referenced :: Int -> m Bool
    referenced n = getReferenced >>= return . (n `Set.member`)

-- ParseState holds all the funny stuff which doesn't respect the parse tree
data ParseState = ParseState {sumbastiBindings::Bindings, nextFreshVar::Int, referencedVars::Set Int}
type ParseM = State ParseState
nullParseState = ParseState Map.empty 0 Set.empty
class (Monad m,Applicative m) => ParseStateful m where
    getParseState :: m ParseState
    putParseState :: ParseState -> m ()
    modifyParseState :: (ParseState -> ParseState) -> m ()
    modifyParseState f = (f <$> getParseState) >>= putParseState

data BridiParseState = BridiParseState {arglist::Arglist,varBindings::VarBindings}
nullBridiParseState = BridiParseState nullArglist Map.empty

type BridiM = (StateT BridiParseState) (ContT Prop ParseM)

runBridiM :: BridiM Prop -> Prop
runBridiM =
    (`evalState` nullParseState) . (`runContT` return) . (`evalStateT` nullBridiParseState)

instance ParseStateful BridiM where
    getParseState = lift get
    putParseState = lift . put
instance Sumbastiful BridiM where
    getSumbastiBindings = sumbastiBindings <$> getParseState
    putSumbastiBindings bs = modifyParseState $ \ps -> ps{sumbastiBindings=bs}
instance Varpool BridiM where
    getNextFresh = nextFreshVar <$> getParseState
    putNextFresh n = modifyParseState $ \ps -> ps{nextFreshVar=n}
    getReferenced = referencedVars <$> getParseState
    putReferenced rv = modifyParseState $ \ps -> ps{referencedVars=rv}

class (Monad m,Applicative m) => Arglistful m where
    getArglist :: m Arglist
    putArglist :: Arglist -> m ()
    modifyArglist :: (Arglist -> Arglist) -> m ()
    modifyArglist f = (f <$> getArglist) >>= putArglist
instance Arglistful BridiM where
    getArglist = arglist <$> get
    putArglist al = modify $ \s -> s{arglist=al}

class (Monad m,Applicative m) => VarBindful m where
    getVarBindings :: m VarBindings
    putVarBindings :: VarBindings -> m ()
    modifyVarBindings :: (VarBindings -> VarBindings) -> m ()
    modifyVarBindings f = (f <$> getVarBindings) >>= putVarBindings
    setVarBinding :: SumtiAtom -> JboTerm -> m ()
    setVarBinding a t = (Map.insert a t <$> getVarBindings) >>= putVarBindings
    lookupVarBinding :: SumtiAtom -> m (Maybe JboTerm)
    lookupVarBinding a = Map.lookup a <$> getVarBindings 
    getVarBinding :: SumtiAtom -> m JboTerm
    getVarBinding a = fromJust <$> lookupVarBinding a
instance VarBindful BridiM where
    getVarBindings = varBindings <$> get
    putVarBindings vbs = modify $ \s -> s{varBindings=vbs}

type Bridi = Args -> Prop

mapProp :: (Prop -> Prop) -> BridiM ()
mapProp f = lift $ ContT $ \k -> f <$> k ()

-- |mapBridiM2 f m1 m2: fork, doing m1 and m2 then joining final Props with f;
--  ParseState threaded through as m1 then m2 then continuation.
mapBridiM2 :: (Prop -> Prop -> Prop) -> BridiM a -> BridiM a -> BridiM a
mapBridiM2 f m1 m2 =
    -- XXX: ugliness warning
    StateT $ \s -> ContT $ \k -> state $ \ps ->
	let e1 = execBridiMParseState m1 s
	    e2 = execBridiMParseState m2 s
	    s1 = runContT (runStateT m1 s) $ (modify e2 >>) . k
	    s2 = runContT (runStateT (lift (modify e1) >> m2) s) k
	    p1 = evalState s1 ps
	    (p2,ps') = runState s2 ps
	in (f p1 p2,ps')

-- |execBridiMParseState m s: extract the ParseState modifications performed
-- in the process of m with initial BridiParseState s
execBridiMParseState :: BridiM a -> BridiParseState -> (ParseState -> ParseState)
execBridiMParseState m s = execState $ (`runContT` (\_ -> return Eet)) $ (`runStateT` s) $ m

updateParseStateWithJboTerm :: JboTerm -> BridiM ()
updateParseStateWithJboTerm o = do
	setSumbasti Ri o
	case o of
	    Named (c:_) -> setSumbasti (LerfuString [c]) o
	    _ -> return ()
	case o of
	    Var n -> setReferenced n
	    _ -> return ()

doAssigns :: JboTerm -> [SumtiAtom] -> BridiM ()
doAssigns o = mapM_ (`setSumbasti` o)

doIncidentals :: JboTerm -> [JboPred] -> BridiM ()
doIncidentals o ips =
    -- TODO
    return ()

advanceArgPosToBridi :: Arglistful m => m ()
advanceArgPosToBridi = modifyArglist $ \al ->
    if Map.null $ args al
       then al{position=2}
       else al

ignoringArgs :: Arglistful m => m a -> m a
ignoringArgs m = do
    al <- getArglist
    m <* putArglist al

partiallyResolveBridi :: (Bridi,BridiParseState) -> Bridi
partiallyResolveBridi (b,s) =
    \extraArgs -> b $ joinArgs (args $ arglist s) extraArgs
resolveBridi :: (Bridi,BridiParseState) -> Prop
resolveBridi (b,s) = partiallyResolveBridi (b,s) nullArgs

parseStatements :: [Statement] -> BridiM Prop
parseStatements ss = mapM parseStatement ss >>= return . bigAnd

parseStatement :: Statement -> BridiM Prop
parseStatement (Statement ps s) = do
    ignoringArgs $ parseTerms ps
    parseStatement1 s

parseStatement1 :: Statement1 -> BridiM Prop
parseStatement1 (ConnectedStatement con s1 s2) =
    do p1 <- parseStatement1 s1
       p2 <- parseStatement1 s2
       return $ connToFOL con p1 p2
parseStatement1 (StatementStatements ss) =
    parseStatements ss
parseStatement1 (StatementSentence s) =
    -- TODO: assign go'i
    runSubBridiM $ parseSentence s

parseSubsentence :: Subsentence -> BridiM Bridi
parseSubsentence (Subsentence ps s) = do
    ignoringArgs $ parseTerms ps
    parseSentence s

runSubBridiM :: BridiM Bridi -> BridiM Prop
runSubBridiM m = do
    s <- get
    p <- lift.lift $ (`runContT` return.resolveBridi) $ (`runStateT` s) $ m
    return $ p


parseSentence :: Sentence -> BridiM Bridi
parseSentence (Sentence ts bt) =
    parseTerms ts >> parseBTail bt

parseBTail :: BridiTail -> BridiM Bridi
parseBTail (GekSentence (ConnectedGS con ss1 ss2 tts)) =
    mapBridiM2 (connToFOL con) (parseSubsentence ss1) (parseSubsentence ss2)
	<* parseTerms tts

parseBTail (GekSentence (NegatedGS gs)) =
    mapProp Not >> parseBTail (GekSentence gs)

parseBTail (ConnectedBT con bt1 bt2 tts) =
    parseBTail (GekSentence (ConnectedGS con
	(Subsentence [] (Sentence [] bt1))
	(Subsentence [] (Sentence [] bt2)) tts))

parseBTail (BridiTail3 (Negated sb) tts) =
    -- XXX: need to handle Negated here as well as in parseSelbri, because of
    -- the SBInverted handling within parseBTail below.
    -- Make sure to do the same for tags when we implement them.
    mapProp Not >> parseBTail (BridiTail3 sb tts)

parseBTail (BridiTail3 (Selbri2 (SBInverted sb sb')) tts) =
    jboRelToBridi <$> getInvertedRel sb sb' where
    getInvertedRel sb sb' = do
	tertau <- parseSelbri3 sb
	seltau <- case sb' of
	    SBInverted sb'' sb''' -> parsedSelbriToPred $ jboRelToBridi <$> getInvertedRel sb'' sb'''
	    Selbri3 sb'' -> selbriToPred $ Selbri2 (Selbri3 (TanruUnit (TUSelbri3 sb'') tts))
	return $ Tanru seltau tertau

parseBTail (BridiTail3 sb tts) = do
    advanceArgPosToBridi
    parseSelbri sb <* parseTerms tts

parseSelbri :: Selbri -> BridiM Bridi
parseSelbri (Negated sb) =
    mapProp Not >> parseSelbri sb
parseSelbri (Selbri2 sb) =
    jboRelToBridi <$> parseSelbri2 sb

-- Note that non-logical connections mean that we can't actually eliminate the
-- ConnectedRels or PermutedRel constructors (consider {se broda joi brode})
jboRelToBridi :: JboRel -> Bridi
jboRelToBridi = jboRelToBridi' . pullOutPermutations where
    jboRelToBridi' (PermutedRel n rel) =
	jboRelToBridi' rel . swapArgs (NPos 1) (NPos n)
    jboRelToBridi' rel = \as -> Rel rel (argsToJboterms as)
    pullOutPermutations r@(Tanru seltau tertau) =
	case pullOutPermutations tertau of
	    PermutedRel n tertau' ->
		PermutedRel n $ pullOutPermutations (Tanru seltau tertau')
	    _ -> r
    pullOutPermutations (PermutedRel n rel) =
	PermutedRel n $ pullOutPermutations rel
    pullOutPermutations rel = rel

parseSelbri2 :: Selbri2 -> BridiM JboRel
parseSelbri2 (SBInverted sb sb') = do
    -- XXX: this works correctly only when there are no tailterms; see
    -- parseBTail above for tailterm handling.
    tertau <- parseSelbri3 sb
    seltau <- selbriToPred $ (Selbri2 sb')
    return $ Tanru seltau tertau

parseSelbri2 (Selbri3 sb) =
    parseSelbri3 sb

parseSelbri3 :: Selbri3 -> BridiM JboRel
parseSelbri3 (SBTanru sb sb') = do
    seltau <- selbriToPred $ (Selbri2 (Selbri3 sb))
    tertau <- parseSelbri3 sb'
    return $ Tanru seltau tertau
parseSelbri3 (ConnectedSB con sb sb') =
    -- XXX: CLL arguably prescribes handling logical connections like
    -- non-logical connections here, with indeterminate semantics; but we
    -- handle them like giheks.
    mapBridiM2 (connToFOL con) (parseSelbri3 sb) (parseSelbri3 sb')
parseSelbri3 (TanruUnit tu2 las) =
    parseTU tu2 <* parseTerms las

parseTU :: TanruUnit2 -> BridiM JboRel
parseTU (TUBrivla bv) = return $ Brivla bv
parseTU (TUMe s) = do
    o <- parseSumti s
    return $ Among o
parseTU (TUMoi q m) = return $ Moi q m
parseTU (TUAbstraction a ss) =
    case
	case a of
	    "poi'i" ->
		 -- poi'i: an experimental NU, which takes ke'a rather
		 -- than ce'u; {ko'a poi'i ke'a broda} means
		 -- {ko'a broda}. See http://www.lojban.org/tiki/poi'i
		 Just RelVar
	    "ka" -> Just LambdaVar
	    "ni" -> Just LambdaVar
	    _ -> Nothing
    of
	Just rv -> do
	    pred <- subsentToPred ss rv
	    return $ AbsPred a pred
	Nothing -> AbsProp a <$>
	    (runSubBridiM $ putArglist nullArglist >> parseSubsentence ss)
parseTU (TUPermuted n tu) =
    PermutedRel n <$> parseTU tu
parseTU (TUSelbri3 sb) = parseSelbri3 sb

parseTerms :: [Term] -> BridiM ()
parseTerms = mapM_ parseTerm

parseTerm :: Term -> BridiM ()
parseTerm t = case t of
    Termset ts -> mapM_ parseTerm ts
    ConnectedTerms con t1 t2 ->
	mapBridiM2 (connToFOL con)
	    (parseTerm t1)
	    (parseTerm t2)
    Negation -> mapProp Not
    Sumti tag s -> do 
	o <- parseSumti s
	addArg $ Arg tag o

parseSumti :: Sumti -> BridiM JboTerm
parseSumti s = do
    (o,ips,as) <- case s of
	(ConnectedSumti con s1 s2 rels) -> do
	    [o1,o2] <- mapM parseSumti [s1,s2]
	    fresh <- getFreshVar
	    mapProp $ \p ->
		connToFOL con
		(subTerm fresh o1 p)
		(subTerm fresh o2 p)
	    (_,ips,as) <- parseRels rels
	    return (fresh,ips,as)
	(QAtom mq rels sa) -> do
	    (rps,ips,as) <- parseRels rels
	    o <- case sa of
		 Variable _ -> parseVariable sa rps mq
		 _ -> do
		     o <- parseSumtiAtom sa
		     case mq of
		       Nothing -> return o
		       Just q -> quantify q $ Just $ isAmong o
	    return (o,ips,as)
	(QSelbri q rels sb) -> do 
	    (rps,ips,as) <- parseRels rels
	    sr <- selbriToPred sb
	    o <- quantify q (andMPred $ sr:rps)
	    return (o,ips,as)
    updateParseStateWithJboTerm o
    doAssigns o as
    doIncidentals o ips
    return o

parseRels :: [RelClause] -> BridiM ([JboPred],[JboPred],[SumtiAtom])
parseRels [] = return ([],[],[])
parseRels (r:rs) = do
    (rps,ips,as) <- case r of
	Restrictive ss -> do
	    rp <- subsentToPred ss RelVar
	    return ([rp],[],[])
	Incidental ss -> do
	    ip <- subsentToPred ss RelVar
	    return ([],[ip],[])
	RestrictiveGOI goi s -> do
	    o <- parseSumti s
	    let rel = case goi of
		    "pe" -> Brivla "srana"
		    "po'u" -> Brivla "du"
		    -- XXX: following are rather approximate... the
		    -- BPFK subordinators section suggests more
		    -- complicated expressions
		    "po'e" -> Tanru (\o -> Rel (Brivla "jinzi") [o])
				(Brivla "srana")
		    "po" -> Tanru (\o -> Rel (Brivla "steci") [o])
				(Brivla "srana")
		rp = \x -> Rel rel [x,o]
	    return ([rp],[],[])
	IncidentalGOI goi s -> do
	    o <- parseSumti s
	    let rel = case goi of
		    "ne" -> Brivla "srana"
		    "no'u" -> Brivla "du"
		ip = \x -> Rel rel [x,o]
	    return ([],[ip],[])
	Assignment (QAtom Nothing [] sa) | isAssignable sa -> 
	    return ([],[],[sa])
	Assignment _ ->
	    -- TODO: handle {mi fa'u do vu'o goi ko'a fa'u ko'e}?
	    return ([],[],[])
    (rps',ips',as') <- parseRels rs
    return (rps++rps',ips++ips',as++as')

isAssignable :: SumtiAtom -> Bool
isAssignable (Assignable _) = True
isAssignable (LerfuString _) = True
isAssignable _ = False

parseVariable sa@(Variable n) rps mq = do
    x <- lookupVarBinding sa
    case x of
	 Nothing -> do
	    o <- quantify (fromMaybe Exists mq) $ andMPred rps
	    setVarBinding sa o
	    return o
	 Just o -> do
	    return o
parseSumtiAtom sa = case sa of
    Description gadri mis miq sb innerRels -> do
	let innerRels' = innerRels
		++ case mis of
		    Nothing -> []
		    Just is -> [IncidentalGOI "ne" is]
	(_,ips,as) <- parseRels innerRels'
	sr <- selbriToPred sb
	let r = andPred $
		   (case miq of
		     Just iq -> [(\o -> Rel (Moi iq "mei") [o])]
		     _ -> []) ++
		   ips ++
		   [sr]
	o <- quantify (Gadri gadri) (Just r)
	doAssigns o as
	return o
    RelVar _ -> getVarBinding sa
    LambdaVar _ -> getVarBinding sa
    anaph@Ri -> getSumbasti sa
    anaph@(Assignable _) -> getSumbasti sa
    anaph@(LerfuString _) -> getSumbasti sa
    NonAnaphoricProsumti ps -> return $ NonAnaph ps
    Name s -> return $ Named s
    Zohe -> return $ ZoheTerm
    Quote t -> return $ JboQuote t
    Word s -> return $ Valsi s


quantify :: Quantifier -> Maybe JboPred -> BridiM JboTerm
quantify q r = do
    fresh <- getFreshVar
    mapProp $ \p ->
	Quantified q (singpred <$> r) $
	    \v -> subTerm fresh (Var v) p
    return fresh
    where
	singpred r = \v -> r (Var v)

selbriToPred :: Selbri -> BridiM JboPred
selbriToPred sb = do
    parsedSelbriToPred $ parseSelbri sb
parsedSelbriToPred :: BridiM Bridi -> BridiM JboPred
parsedSelbriToPred m = do
    fresh <- getFreshVar
    p <- runSubBridiM $ putArglist nullArglist >> m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> BridiM JboPred
subsentToPred ss rv = do
    fresh@(Var n) <- getFreshVar
    p <- runSubBridiM $ do
	modifyVarBindings $ shuntVars rv
	setVarBinding (rv 1) fresh
	p <- putArglist nullArglist >> parseSubsentence ss
	reffed <- referenced n
	when (not reffed) $ addImplicit fresh
	return p
    return $ \o -> subTerm fresh o p


shuntVars :: (Int -> SumtiAtom) -> Bindings -> Bindings
shuntVars var bs = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 1 .. head [ n-1 | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]

andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]

andMPred :: [JboPred] -> Maybe JboPred
andMPred [] = Nothing
andMPred ps = Just $ andPred ps

isAmong :: JboTerm -> (JboTerm -> Prop)
isAmong y = \o -> Rel (Among y) [o]

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
instance JboShow Connective where
    logjboshow _ (Connective b c b') =
	return $ (if not b then "na." else "") ++
	    [c] ++
	    if not b' then "nai" else ""

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
    logjboshow jbo (ConnectedRels conn r r') = do
	s <- logjboshow jbo r
	s' <- logjboshow jbo conn
	s'' <- logjboshow jbo r'
	return $ if jbo
	    then s ++ " " ++ s' ++ " " ++ s''
	    else "(" ++ s ++ " " ++ s' ++ " " ++ s'' ++ ")"
    logjboshow jbo (PermutedRel n r) =
	((seToStr n ++ " ") ++) <$> logjboshow jbo r
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
    logjboshow jbo (Among t) = do
	s <- logjboshow jbo t
	return $ if jbo then "me " ++ s ++ " me'u" else "Among[" ++ s ++ "]"
    logjboshow _ (Brivla s) = return s

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
