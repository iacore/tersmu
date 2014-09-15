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
    , variableDomains :: Map Int VariableDomain
    , nextFreshConstant::Int
    , referencedVars::Set Int
    , questions::[Question]
    , lambdas::Map LambdaPos Int
    , freeDict::Map Int Free
    , sideTexticules::[Texticule]
    }
nullParseState = ParseState Map.empty Map.empty 0 Map.empty 0 Set.empty [] Map.empty Map.empty []
type ParseStateT = StateT ParseState
type ParseStateM = ParseStateT Identity

-- BridiParseState holds state which respects the logical structure
data BridiParseState = BridiParseState {arglist::Arglist,varBindings::VarBindings,isSubBridi::Bool}
nullBridiParseState = BridiParseState nullArglist Map.empty False

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

type BribastiBindings = Map TanruUnit Bridi

data Question = Question {qKauDepth :: Maybe Int, qInfo::QInfo}
data QInfo
    = QTruth
    | QSumti JboTerm

data LambdaPos = LambdaPos {lambdaLevel :: Int, lambdaNum :: Int}
    deriving (Eq, Show, Ord)

data VariableDomain = UnrestrictedDomain | FiniteDomain [JboTerm] | PredDomain JboPred
    deriving (Eq, Show, Ord)

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
    modifyBribastiBindings :: (BribastiBindings -> BribastiBindings) -> m ()
    modifyBribastiBindings f = (f <$> getBribastiBindings) >>= putBribastiBindings
    setBribasti :: TanruUnit -> Bridi -> m ()
    setBribasti s b = (Map.insert s b <$> getBribastiBindings) >>= putBribastiBindings
    getBribasti :: TanruUnit -> m Bridi
    getBribasti s = (`getBribastiBinding` s) <$> getBribastiBindings

    getNextFreshVar :: m Int
    getNextFreshVar = nextFreshVar <$> getParseState
    putNextFreshVar :: Int -> m ()
    putNextFreshVar n = modifyParseState $ \ps -> ps{nextFreshVar=n}
    modifyDomains :: (Map Int VariableDomain -> Map Int VariableDomain) -> m ()
    modifyDomains f = modifyParseState $ \ps -> ps{variableDomains = f $ variableDomains ps}
    setDomain :: JboTerm -> VariableDomain -> m ()
    setDomain (Var n) dom = modifyDomains $ Map.insert n dom
    setDomain _ _ = return ()
    getDomain :: JboTerm -> m VariableDomain
    getDomain (Var n) = Map.findWithDefault UnrestrictedDomain n . variableDomains <$> getParseState
    getDomain _ = return UnrestrictedDomain
    modifyDomain :: JboTerm -> (VariableDomain -> VariableDomain) -> m ()
    modifyDomain (Var n) f = modifyDomains $ Map.adjust f n
    getNextFreshConstant :: m Int
    getNextFreshConstant = nextFreshConstant <$> getParseState
    putNextFreshConstant :: Int -> m ()
    putNextFreshConstant n = modifyParseState $ \ps -> ps{nextFreshConstant=n}
    getReferenced :: m (Set Int)
    getReferenced = referencedVars <$> getParseState
    putReferenced :: Set Int -> m ()
    putReferenced rv = modifyParseState $ \ps -> ps{referencedVars=rv}

    getFreshVar :: VariableDomain -> m JboTerm
    -- note: crucial that we don't reuse variables, so we can catch "donkey
    -- sentences" which involve scope-breaking sumbasti references to unbound
    -- variables (e.g. {ro tercange poi ponse su'o xasli cu darxi ri}).
    getFreshVar dom = do
	n <- getNextFreshVar
	putNextFreshVar $ n+1
	setDomain (Var n) dom
	return $ Var n
    getFreshConstant :: m JboTerm
    getFreshConstant = do
	n <- getNextFreshConstant
	putNextFreshConstant $ n+1
	return $ Constant n []
    setReferenced :: Int -> m ()
    setReferenced n = getReferenced >>= putReferenced . Set.insert n
    referenced :: Int -> m Bool
    referenced n = getReferenced >>= return . (n `Set.member`)

    addQuestion :: Question -> m ()
    addQuestion b = modifyParseState $ \ps -> ps{questions=b:questions ps}
    modifyQuestions :: ([Question] -> [Question]) -> m ()
    modifyQuestions f = modifyParseState $ \ps ->
		ps{questions = f $ questions ps}

    putLambda :: Maybe Int -> Maybe Int -> m JboTerm
    putLambda mlev mnum = do
	ls <- lambdas <$> getParseState
	let lev = fromMaybe 1 mlev
	    next = maximum (0:[ n | LambdaPos l n <- Map.keys ls, l==lev ]) + 1
	    num = fromMaybe next mnum
	    pos = LambdaPos lev num
	    mn = Map.lookup pos ls
	case mn of
	    Just n -> return $ Var n
	    Nothing -> do
		fresh@(Var n) <- getFreshVar UnrestrictedDomain
		modifyLambdas $ Map.insert pos n
		return fresh
    modifyLambdas :: (Map LambdaPos Int -> Map LambdaPos Int) -> m ()
    modifyLambdas f = modifyParseState $ \ps ->
		ps{lambdas = f $ lambdas ps}
    shuntLambdas :: Int -> m ()
    shuntLambdas d = modifyLambdas $
	Map.filterWithKey (\(LambdaPos l _) _ -> l > 0)
	. Map.mapKeys (\(LambdaPos l n) -> LambdaPos (l+d) n)

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
	    Nothing -> UnboundSumbasti a

getBribastiBinding :: BribastiBindings -> TanruUnit -> Bridi
getBribastiBinding bs bb =
    case Map.lookup bb bs of
	Just b -> b
	Nothing -> jboRelToBridi $ case bb of
	    TUBrivla s -> Brivla s
	    _ -> UnboundBribasti bb


addSideTexticule :: ParseStateful m => Texticule -> m ()
addSideTexticule side =
    modifyParseState $ \pst -> pst{sideTexticules=side:sideTexticules pst}

takeSideTexticules :: ParseStateful m => m [Texticule]
takeSideTexticules =
    (sideTexticules <$> getParseState)
	<* (modifyParseState $ \pst -> pst{sideTexticules=[]})


addSumtiQuestion :: ParseStateful m => Maybe Int -> m JboTerm
addSumtiQuestion kau = do
    o <- getFreshVar UnrestrictedDomain
    addQuestion $ Question kau $ QSumti o
    return o
withQuestions :: (ParseStateful m, PreProp p) => Bool -> m p -> m p
withQuestions top m = do
    -- XXX: using ParseState for this is a bit of a hack, really, but I'd
    -- rather not add another layer to the monad stack.
    qs <- questions <$> getParseState
    modifyQuestions $ const []
    (doQuestions top =<< m) <* (modifyQuestions (qs++))
doQuestions :: (ParseStateful m, PreProp p) => Bool -> p -> m p
doQuestions top p =
    foldl (flip doQInfo) p <$> deKau top
doQInfo :: PreProp p => QInfo -> p -> p
doQInfo (QSumti qv) = liftToProp $ \p ->
    -- TODO: really, this ought to use a plural variable
    Quantified QuestionQuantifier Nothing $
	\v -> subTerm qv (BoundVar v) p
doQInfo QTruth = liftToProp $ Modal QTruthModal
deKau :: ParseStateful m => Bool -> m [QInfo]
deKau top = do
    qs <- questions <$> getParseState
    let deKauq q = if top || qKauDepth q == Just 1
		then Left q
		else Right q {qKauDepth = (+(-1))<$>qKauDepth q}
	(outqs,qs') = partitionEithers $ map deKauq qs
    modifyQuestions $ const qs'
    return $ map qInfo outqs

doLambdas :: JboVPred -> ParseM r JboNPred
doLambdas vpred = do
    ls <- lambdas <$> getParseState
    let arity = maximum $ 1:[n | LambdaPos 1 n <- Map.keys ls]
	apply vpred (n,o) = case Map.lookup (LambdaPos 1 n) ls of
	    Nothing -> \os -> vpred $ o:os
	    Just v -> \os -> subTerm (Var v) o $ vpred os
    shuntLambdas (-1)
    return $ JboNPred arity $ \os -> foldl apply vpred (zip [1..] os) []

data Arglist = Arglist {args :: Args, position::Int}
type Args = Map ArgPos JboTerm
data ArgPos = NPos Int | JaiPos | UnfilledPos Int
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
joinArgs new old = Map.union new $ oldWithImplicits where
    oldWithImplicits = foldl insertImplicit old
	[o | (UnfilledPos _, o) <- Map.assocs new]
    insertImplicit as o = 
	let gap = head $ [1..] \\ [n | NPos n <- Map.keys $ as]
	in Map.insert (NPos gap) o $ as

swapArgs :: ArgPos -> ArgPos -> Args -> Args
swapArgs p1 p2 = Map.mapKeys (\p -> if p == p1 then p2 else if p == p2 then p1 else p)

setArg :: ArgPos -> JboTerm -> Args -> Args
setArg = Map.insert

addFaiToArglist :: JboTerm -> Arglist -> Arglist
addFaiToArglist o (Arglist as n) = Arglist (Map.insert (JaiPos) o as) n

advanceArgPosToBridi :: Arglistful m => m ()
advanceArgPosToBridi = modifyArglist $ \al ->
    if Map.null $ args al
       then al{position=2}
       else al

ignoringArgs :: Arglistful m => m a -> m a
ignoringArgs m = do
    al <- getArglist
    m <* putArglist al

argsToJboterms :: Args -> [JboTerm]
argsToJboterms as =
    map (\n -> Map.findWithDefault Unfilled (NPos n) as) [1..max as]
    where
	max as = maximum $ 1:[n | NPos n <- Map.keys as]

bridiToJboVPred :: Bridi -> JboVPred
bridiToJboVPred b os =
    b $ Map.fromList [(UnfilledPos n,o) | (n,o) <- zip [0..] os]
bridiToJboPred :: Bridi -> JboPred
bridiToJboPred b = vPredToPred $ bridiToJboVPred b

swapTerms :: [JboTerm] -> Int -> Int -> [JboTerm]
swapTerms ts n m = swapFiniteWithDefault Unfilled ts (n-1) (m-1)

data Arg = Arg Tagged JboTerm
addArg :: PreProp r => Arg -> ParseM r ()
addArg (Arg FAITagged o) = modifyArglist $ addFaiToArglist o
addArg (Arg tag o) = do
    al <- getArglist
    let n = case tag of
	    Untagged -> position al
	    FATagged n -> n
    setArgInArglist (NPos n) o
    isMainBridi <- not . isSubBridi <$> get
    when isMainBridi $ mapProp $ subTerm (UnboundSumbasti $ MainBridiSumbasti n) o
    setArgPos $ n+1
setArgInArglist p o = modifyArglist $ \al -> al{args = setArg p o $ args al}
setArgPos n = modifyArglist $ \al -> al{position=n}

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
    getVarBinding a = do
	mv <- lookupVarBinding a
	case mv of
	    Just v -> return v
	    Nothing -> error $ "Unbound variable " ++ show a
instance VarBindful (ParseM r) where
    getVarBindings = varBindings <$> get
    putVarBindings vbs = modify $ \s -> s{varBindings=vbs}

shuntVars :: Ord a => (Int -> a) -> Map a b -> Map a b
shuntVars var bs = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 1 .. head [ n-1 | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]

setShunting :: Ord a => (Int -> a) -> b -> Map a b -> Map a b
setShunting var b = Map.insert (var 1) b . shuntVars var


class PreProp r where
    liftToProp :: (JboProp -> JboProp) -> r -> r
    liftToProp2 :: (JboProp -> JboProp -> JboProp) -> r -> r -> r
    dummyPreProp :: r
instance PreProp JboProp where
    liftToProp = id
    liftToProp2 = id
    dummyPreProp = Eet
instance PreProp (a -> JboProp) where
    liftToProp = liftA
    liftToProp2 = liftA2
    dummyPreProp = \_ -> Eet
instance PreProp p => PreProp (Maybe p) where
    liftToProp = liftA . liftToProp
    liftToProp2 = liftA2 . liftToProp2
    dummyPreProp = Nothing
instance PreProp JboFragment where
    -- null instance
    liftToProp = \_ -> id
    liftToProp2 = \_ -> \_ -> id
    dummyPreProp = JboFragTerms []

mapProp :: (PreProp r) => (JboProp -> JboProp) -> ParseM r ()
mapProp f = lift $ ContT $ \k -> (liftToProp f) <$> k ()

-- |mapParseM2 f m1 m2: fork, doing m1 and m2 then joining final Props with f;
--  ParseState threaded through as m1 then m2 then continuation.
--  For this to make sense and be symmetric, it is necessary that the
--  ParseState changes caused by the continuation do not depend on which
--  branch it is evaluated in. To ensure this, variable bindings introduced in
--  m1 and m2 are ignored - consider {ko'a .e da broda zo'e ne da} to see why.
mapParseM2 :: (PreProp r) => (JboProp -> JboProp -> JboProp) -> ParseM r a -> ParseM r a -> ParseM r a
mapParseM2 f m1 m2 =
    -- XXX: ugliness warning
    StateT $ \s -> ContT $ \k -> state $ \ps ->
	let e1 = execParseMParseState m1 s
	    e2 = execParseMParseState m2 s
	    [m1',m2'] = map (<* putVarBindings (varBindings s)) [m1,m2]
	    s1 = runContT (runStateT m1' s) $ (modify e2 >>) . k
	    s2 = runContT (runStateT (lift (modify e1) >> m2') s) k
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
runSubBridiM m = ($nullArgs) <$> partiallyRunSubBridiM m

partiallyRunSubBridiM :: BridiM Bridi -> ParseM r Bridi
partiallyRunSubBridiM m = partiallyRunBridiM $ do
    modify $ \s -> s{isSubBridi=True}
    putArglist nullArglist
    m

partiallyRunBridiM :: BridiM Bridi -> ParseM r Bridi
partiallyRunBridiM m = do
    s <- get
    lift.lift $ (`runContT` return.partiallyResolveBridi) $ (`runStateT` s) $ m

setBribastiToCurrent :: TanruUnit -> BridiM ()
setBribastiToCurrent bb =
    -- XXX: results often counterintuitive, probably not what CLL intended
    -- (e.g. {da broda cei brode .i brode} is a donkey, but
    -- {broda cei brode fa da .i brode} is fine).
    lift $ ContT $ \k -> do 
	b <- k () 
	setBribasti bb b
	return b

updateSumbastiWithSumtiAtom :: SumtiAtom -> JboTerm -> ParseM r ()
updateSumbastiWithSumtiAtom sa o = do
    when (getsRi sa) $
	modifySumbastiBindings $ setShunting (\n -> Sumbasti False $ Ri n) o
    case sa of
	Name _ _ s ->
	    setSumbasti (Sumbasti False $ LerfuString $ map LerfuChar $ take 1 s) o
	Description _ _ _ (Left sb) _ _ ->
	    let ls = lerfuStringsOfSelbri sb
	    in mapM_ (`setSumbasti` o) $
		map (Sumbasti False . LerfuString) ls
	_ -> return ()

updateReferenced :: JboTerm -> ParseM r ()
updateReferenced (Var n) = setReferenced n
updateReferenced _ = return ()

doAssigns :: JboTerm -> [Either SumtiAtom JboTerm] -> ParseM r JboTerm
doAssigns = foldM doAssign
doAssign :: JboTerm -> Either SumtiAtom JboTerm -> ParseM r JboTerm
doAssign (UnboundSumbasti a) (Right assto) | isAssignable a =
    setSumbasti (Sumbasti True a) assto >> return assto
doAssign o (Left ass) = setSumbasti (Sumbasti True ass) o >> return o
doAssign o _ = return o

doIncidentals :: JboTerm -> [JboPred] -> ParseM r JboTerm
doIncidentals o ips = case andMPred ips of
    Nothing -> return o
    Just pred -> do
	(pred',o') <- quantifyOutFrees True pred o
	addSideTexticule $ TexticuleProp $ pred' o'
	return o'
    where
	quantifyOutFrees addParams pred o =
	    let frees = nub $ freeVars $ pred o
	    in if null frees
		then return (pred,o)
		else do
		    let o' = case (addParams,o) of
			    (True,Constant n params) ->
				Constant n $ reverse frees ++ params
			    _ -> o
		    pred' <- foldM quantifyOutFree pred frees
		    quantifyOutFrees False pred' o'
	quantifyOutFree pred free = do
	    dom <- getDomain free
	    return $ \x -> Quantified (LojQuantifier Forall)
		(jboPredToLojPred <$> restrOfDom dom)
		$ \v -> subTerm free (BoundVar v) $ pred x
	restrOfDom UnrestrictedDomain = Nothing
	restrOfDom (PredDomain p) = Just p
	restrOfDom (FiniteDomain []) = Nothing
	restrOfDom (FiniteDomain (o:os)) = Just
	    (\x -> foldr (Connected Or) (Rel Equal [x,o]) [Rel Equal [x,o'] | o' <- os])

doIncidental o ip = doIncidentals o [ip]
