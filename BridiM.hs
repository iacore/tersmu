module BridiM where

import JboProp
import JboSyntax
import Util
import FOL hiding (Term)

import Data.Maybe
import Control.Applicative
import Data.List
import Data.Either
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State
import Control.Monad.Cont
import Control.Monad.Identity

-- ParseState holds all the funny stuff which doesn't respect the tree
-- structure of the logical parse; it is threaded through as we parse the text
-- left-to-right.
data ParseState = ParseState
    { sumbastiBindings::SumbastiBindings
    , bribastiBindings::BribastiBindings
    , nextFreshVar::Int
    , nextFreshConstant::Int
    , referencedVars::Set Int
    , questions::[Question]
    , freeDict::Map Int Free
    , sideSentences::[JboProp]
    }
nullParseState = ParseState Map.empty Map.empty 0 0 Set.empty [] Map.empty []
type ParseStateT = StateT ParseState
type ParseStateM = ParseStateT Identity

-- BridiParseState holds state which respects the logical structure
data BridiParseState = BridiParseState {arglist::Arglist,varBindings::VarBindings}
nullBridiParseState = BridiParseState nullArglist Map.empty

type ParseM r = (StateT BridiParseState) (ContT r ParseStateM)
type BridiM = ParseM Bridi
type JboPropM = ParseM JboProp

evalParseStateT :: Monad m => ParseStateT m a -> m a
evalParseStateT = (`evalStateT` nullParseState)
evalParseStateM = runIdentity . evalParseStateT

evalParseM :: ParseM r r -> ParseStateM r
evalParseM =
	(`runContT` return)
	. (`evalStateT` nullBridiParseState)

liftParseStateMToParseM :: ParseStateM a -> ParseM r a
liftParseStateMToParseM = lift.lift

-- |Sumbasti: we differentiate between lerfu strings explicitly assigned with
-- goi and those getting implicit referents based on first letters of
-- names / description selbri; explicit assignations take priority.
data Sumbasti = Sumbasti
    {sumbastiExplicitlyAssigned::Bool, sumbastiAtom::SumtiAtom}
    deriving (Eq, Show, Ord)
type SumbastiBindings = Map Sumbasti JboTerm

type BribastiBindings = Map String Bridi

data Question = Question {qKauDepth :: Maybe Int, qInfo::QInfo}
data QInfo
    = QTruth
    | QSumti JboTerm

class (Monad m,Applicative m) => ParseStateful m where
    getParseState :: m ParseState
    putParseState :: ParseState -> m ()
    modifyParseState :: (ParseState -> ParseState) -> m ()
    modifyParseState f = (f <$> getParseState) >>= putParseState

    getSumbastiBindings :: m SumbastiBindings
    getSumbastiBindings = sumbastiBindings <$> getParseState
    putSumbastiBindings :: SumbastiBindings -> m ()
    putSumbastiBindings bs = modifyParseState $ \ps -> ps{sumbastiBindings=bs}
    modifySumbastiBindings :: (SumbastiBindings -> SumbastiBindings) -> m ()
    modifySumbastiBindings f = (f <$> getSumbastiBindings) >>= putSumbastiBindings
    setSumbasti :: Sumbasti -> JboTerm -> m ()
    setSumbasti a t = (Map.insert a t <$> getSumbastiBindings) >>= putSumbastiBindings
    getSumbasti :: SumtiAtom -> m JboTerm
    getSumbasti a = (`getSumbastiBinding` a) <$> getSumbastiBindings

    getBribastiBindings :: m BribastiBindings
    getBribastiBindings = bribastiBindings <$> getParseState
    putBribastiBindings :: BribastiBindings -> m ()
    putBribastiBindings bs = modifyParseState $ \ps -> ps{bribastiBindings=bs}
    setBribasti :: String -> Bridi -> m ()
    setBribasti s b = (Map.insert s b <$> getBribastiBindings) >>= putBribastiBindings
    getBribasti :: String -> m Bridi
    getBribasti s = (`getBribastiBinding` s) <$> getBribastiBindings

    getNextFreshVar :: m Int
    getNextFreshVar = nextFreshVar <$> getParseState
    putNextFreshVar :: Int -> m ()
    putNextFreshVar n = modifyParseState $ \ps -> ps{nextFreshVar=n}
    getNextFreshConstant :: m Int
    getNextFreshConstant = nextFreshConstant <$> getParseState
    putNextFreshConstant :: Int -> m ()
    putNextFreshConstant n = modifyParseState $ \ps -> ps{nextFreshConstant=n}
    getReferenced :: m (Set Int)
    getReferenced = referencedVars <$> getParseState
    putReferenced :: Set Int -> m ()
    putReferenced rv = modifyParseState $ \ps -> ps{referencedVars=rv}

    getFreshVar :: m JboTerm
    -- note: crucial that we don't reuse variables, so we can catch "donkey
    -- sentences" which involve scope-breaking sumbasti references to unbound
    -- variables (e.g. {ro tercange poi ponse su'o xasli cu darxi ri}).
    getFreshVar = do
	n <- getNextFreshVar
	putNextFreshVar $ n+1
	return $ PreVar n
    getFreshConstant :: m JboTerm
    getFreshConstant = do
	n <- getNextFreshConstant
	putNextFreshConstant $ n+1
	return $ Constant n
    setReferenced :: Int -> m ()
    setReferenced n = getReferenced >>= putReferenced . Set.insert n
    referenced :: Int -> m Bool
    referenced n = getReferenced >>= return . (n `Set.member`)

    addQuestion :: Question -> m ()
    addQuestion b = modifyParseState $ \ps -> ps{questions=b:questions ps}

    putFreeDict :: Map Int Free -> m ()
    putFreeDict d = modifyParseState $ \ps -> ps{freeDict = d}
    setFrees :: [Free] -> m ()
    setFrees fs = putFreeDict $ Map.fromList $ zip [0..] fs
    lookupFree :: Int -> m Free
    lookupFree n = do
	d <- freeDict <$> getParseState
	case Map.lookup n d of
	    Just f -> return f
	    Nothing -> error "No such free!"
instance (Monad m,Functor m) => ParseStateful (ParseStateT m) where
    getParseState = get
    putParseState = put
instance ParseStateful (ParseM r) where
    getParseState = lift get
    putParseState = lift . put

getSumbastiBinding :: SumbastiBindings -> SumtiAtom -> JboTerm
getSumbastiBinding bs a =
    case Map.lookup (Sumbasti True a) bs of
	Just o -> o
	Nothing -> case Map.lookup (Sumbasti False a) bs of 
	    Just o -> o
	    Nothing -> case a of
		Assignable n -> UnboundAssignable n
		LerfuString s -> UnboundLerfuString s
		_ -> error $ show a ++ " not bound.\n"

getBribastiBinding :: BribastiBindings -> String -> Bridi
getBribastiBinding bs s =
    case Map.lookup s bs of
      Just b -> b
      Nothing -> jboRelToBridi $ Brivla s


addSideSentence :: ParseStateful m => JboProp -> m ()
addSideSentence p =
    modifyParseState $ \pst -> pst{sideSentences=p:sideSentences pst}

takeSideSentence :: ParseStateful m => m [JboProp]
takeSideSentence =
    (sideSentences <$> getParseState)
	<* (modifyParseState $ \pst -> pst{sideSentences=[]})


addSumtiQuestion :: ParseStateful m => Maybe Int -> m JboTerm
addSumtiQuestion kau = do
    o <- getFreshVar
    addQuestion $ Question kau $ QSumti o
    return o
doQuestions :: ParseStateful m => Bool -> JboProp -> m JboProp
doQuestions top p =
    foldr doQInfo p <$> deKau top
doQuestionsPred :: ParseStateful m => Bool -> JboPred -> m JboPred
doQuestionsPred top p =
    deKau top >>= \qs -> return $ \o -> foldr doQInfo (p o) qs
doQInfo :: QInfo -> JboProp -> JboProp
doQInfo (QSumti qv) p = Quantified QuestionQuantifier Nothing $
	\v -> subTerm qv (Var v) p
doQInfo QTruth p = Modal QTruthModal p
deKau :: ParseStateful m => Bool -> m [QInfo]
deKau top = do
    qs <- questions <$> getParseState
    let deKauq q = if top || qKauDepth q == Just 1
		then Left q
		else Right q {qKauDepth = (+(-1))<$>qKauDepth q}
	(outqs,qs') = partitionEithers $ map deKauq qs
    modifyParseState $ \ps -> ps{questions = qs'}
    return $ map qInfo outqs

data Arglist = Arglist {args :: Args, position::Int}
type Args = Map ArgPos JboTerm
data ArgPos = NPos Int | JaiPos
    deriving (Eq, Show, Ord)
class (Monad m,Applicative m) => Arglistful m where
    getArglist :: m Arglist
    putArglist :: Arglist -> m ()
    modifyArglist :: (Arglist -> Arglist) -> m ()
    modifyArglist f = (f <$> getArglist) >>= putArglist
instance Arglistful (ParseM r) where
    getArglist = arglist <$> get
    putArglist al = modify $ \s -> s{arglist=al}

type Bridi = Args -> JboProp
jboRelToBridi :: JboRel -> Bridi
jboRelToBridi rel = \as -> Rel rel (argsToJboterms as)

withJaiAsTag :: JboTag -> Bridi -> Bridi
withJaiAsTag jtag b = \as -> case Map.lookup JaiPos as of
    Nothing -> b as
    Just a -> Modal (JboTagged jtag $ Just a) $ b (Map.delete JaiPos as)

withJaiAsRaising :: Bridi -> Bridi
withJaiAsRaising b = \as -> case Map.lookup JaiPos as of
    Nothing -> b as
    Just a -> b (setArg (NPos 1) (QualifiedTerm (LAhE "tu'a") a) as)

nullArgs = Map.empty
nullArglist = Arglist nullArgs 1

joinArgs :: Args -> Args -> Args
joinArgs = Map.union

swapArgs :: ArgPos -> ArgPos -> Args -> Args
swapArgs p1 p2 = Map.mapKeys (\p -> if p == p1 then p2 else if p == p2 then p1 else p)

setArg :: ArgPos -> JboTerm -> Args -> Args
setArg = Map.insert

appendToArglist :: JboTerm -> Arglist -> Arglist
appendToArglist o (Arglist as n) = Arglist (Map.insert (NPos n) o as) (n+1)

addFaiToArglist :: JboTerm -> Arglist -> Arglist
addFaiToArglist o (Arglist as n) = Arglist (Map.insert (JaiPos) o as) n

advanceArgPosToBridi :: Arglistful m => m ()
advanceArgPosToBridi = modifyArglist $ \al ->
    if Map.null $ args al
       then al{position=2}
       else al
setArgPos n = modifyArglist $ \al -> al{position=n}

ignoringArgs :: Arglistful m => m a -> m a
ignoringArgs m = do
    al <- getArglist
    m <* putArglist al

argsToJboterms :: Args -> [JboTerm]
argsToJboterms as = map (\n -> Map.findWithDefault ZoheTerm (NPos n) as) [1..max] where
    max = maximum $ 1:[n | NPos n <- Map.keys as]

swapTerms :: [JboTerm] -> Int -> Int -> [JboTerm]
swapTerms ts n m = take (max (max n m) (length ts)) $
	swap (ts ++ (repeat ZoheTerm)) (n-1) (m-1)

-- | addImplicit: adds a jboterm at first empty positional slot
addImplicit :: JboTerm -> ParseM r ()
addImplicit o = modifyArglist $ \al ->
    let as = args al
	gap = head $ [1..] \\ [n | NPos n <- Map.keys as]
    in al{args=(Map.insert (NPos gap) o as)}

data Arg = Arg Tagged JboTerm
addArg :: Arg -> ParseM r ()
addArg (Arg FAITagged o) = modifyArglist $ addFaiToArglist o
addArg (Arg tag o) = modifyArglist $
	(appendToArglist o) .
	(\as -> case tag of
	    Untagged -> as
	    FATagged n -> as{position=n}
	    Tagged _ -> error "Now how did that get here?")

type VarBindings = Map SumtiAtom JboTerm
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
instance VarBindful (ParseM r) where
    getVarBindings = varBindings <$> get
    putVarBindings vbs = modify $ \s -> s{varBindings=vbs}

shuntVars :: Ord a => (Int -> a) -> Map a b -> Map a b
shuntVars var bs = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 1 .. head [ n-1 | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]


class PreProp r where
    liftToProp :: (JboProp -> JboProp) -> r -> r
    liftToProp2 :: (JboProp -> JboProp -> JboProp) -> r -> r -> r
    dummyPreProp :: r
instance PreProp JboProp where
    liftToProp = id
    liftToProp2 = id
    dummyPreProp = Eet
instance PreProp Bridi where
    liftToProp = liftA
    liftToProp2 = liftA2
    dummyPreProp = \_ -> Eet

mapProp :: (PreProp r) => (JboProp -> JboProp) -> ParseM r ()
mapProp f = lift $ ContT $ \k -> (liftToProp f) <$> k ()

-- |mapParseM2 f m1 m2: fork, doing m1 and m2 then joining final Props with f;
--  ParseState threaded through as m1 then m2 then continuation.
mapParseM2 :: (PreProp r) => (JboProp -> JboProp -> JboProp) -> ParseM r a -> ParseM r a -> ParseM r a
mapParseM2 f m1 m2 =
    -- XXX: ugliness warning
    StateT $ \s -> ContT $ \k -> state $ \ps ->
	let e1 = execParseMParseState m1 s
	    e2 = execParseMParseState m2 s
	    s1 = runContT (runStateT m1 s) $ (modify e2 >>) . k
	    s2 = runContT (runStateT (lift (modify e1) >> m2) s) k
	    r1 = evalState s1 ps
	    (r2,ps') = runState s2 ps
	in ((liftToProp2 f) r1 r2,ps')

-- |execParseMParseState m s: extract the ParseState modifications performed
-- in the process of m with initial BridiParseState s
execParseMParseState :: PreProp r => ParseM r a -> BridiParseState -> (ParseState -> ParseState)
execParseMParseState m s = execState $ (`runContT` (\_ -> return dummyPreProp)) $ (`runStateT` s) $ m

partiallyResolveBridi :: (Bridi,BridiParseState) -> Bridi
partiallyResolveBridi (b,s) =
    \extraArgs -> b $ joinArgs extraArgs (args $ arglist s)
resolveBridi :: (Bridi,BridiParseState) -> JboProp
resolveBridi (b,s) = partiallyResolveBridi (b,s) nullArgs

runSubBridiM :: BridiM Bridi -> ParseM r JboProp
runSubBridiM m = ($nullArgs) <$> partiallyRunBridiM (putArglist nullArglist >> m)

partiallyRunBridiM :: BridiM Bridi -> ParseM r Bridi
partiallyRunBridiM m = do
    s <- get
    lift.lift $ (`runContT` return.partiallyResolveBridi) $ (`runStateT` s) $ m

setBribastiToCurrent :: String -> BridiM ()
setBribastiToCurrent bv =
    -- XXX: results often counterintuitive, probably not what CLL intended
    -- (e.g. {da broda cei brode .i brode} is a donkey, but
    -- {broda cei brode fa da .i brode} is fine).
    lift $ ContT $ \k -> do 
	b <- k () 
	setBribasti bv b
	return b

updateSumbastiWithSumtiAtom :: SumtiAtom -> JboTerm -> ParseM r ()
updateSumbastiWithSumtiAtom sa o = do
    when (getsRi sa) $ do
	modifySumbastiBindings $ shuntVars $ \n -> Sumbasti False $ Ri n
	setSumbasti (Sumbasti False $ Ri 1) o
    case sa of
	Name _ s ->
	    setSumbasti (Sumbasti False $ LerfuString $ take 1 s) o
	Description _ _ _ sb _ _ ->
	    let ls = lerfuStringOfSelbri sb
	    in mapM_ (`setSumbasti` o) $
		map (Sumbasti False . LerfuString) [ls, take 1 ls]
	_ -> return ()

updateReferenced :: JboTerm -> ParseM r ()
updateReferenced (PreVar n) = setReferenced n
updateReferenced _ = return ()

doAssigns :: JboTerm -> [Either SumtiAtom JboTerm] -> ParseM r JboTerm
doAssigns o as = case o of
    UnboundAssignable _ -> assignRight o $ rights as
    UnboundLerfuString _ -> assignRight o $ rights as
    _ -> mapM_ (`setSumbasti` o) (map (Sumbasti True) $ lefts as) >> return o
    where
	assignRight o [] = return o
	assignRight o ras = let ra = last ras
	    in setSumbasti (Sumbasti True $ sumtiAtomOfUnbound o) ra >> return ra
	sumtiAtomOfUnbound (UnboundAssignable n) = Assignable n
	sumtiAtomOfUnbound (UnboundLerfuString n) = LerfuString n

doIncidentals :: JboTerm -> [JboPred] -> ParseM r ()
doIncidentals o ips = case andMPred ips of
    Nothing -> return ()
    Just p -> addSideSentence $ p o
