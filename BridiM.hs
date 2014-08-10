module BridiM where

import JboProp
import JboSyntax
import Util
import FOL hiding (Term)

import Data.Maybe
import Control.Applicative
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State
import Control.Monad.Cont

-- ParseState holds all the funny stuff which doesn't respect the tree
-- structure of the logical parse; it is threaded through as we parse the text
-- left-to-right.
data ParseState = ParseState {sumbastiBindings::Bindings, nextFreshVar::Int, referencedVars::Set Int}
nullParseState = ParseState Map.empty 0 Set.empty

-- BridiParseState holds state which respects the logical structure
data BridiParseState = BridiParseState {arglist::Arglist,varBindings::VarBindings}
nullBridiParseState = BridiParseState nullArglist Map.empty

type BridiM = (StateT BridiParseState) (ContT JboProp (State ParseState))

runBridiM :: BridiM JboProp -> JboProp
runBridiM =
    (`evalState` nullParseState) . (`runContT` return) . (`evalStateT` nullBridiParseState)

class (Monad m,Applicative m) => ParseStateful m where
    getParseState :: m ParseState
    putParseState :: ParseState -> m ()
    modifyParseState :: (ParseState -> ParseState) -> m ()
    modifyParseState f = (f <$> getParseState) >>= putParseState
instance ParseStateful BridiM where
    getParseState = lift get
    putParseState = lift . put

type Bindings = Map SumtiAtom JboTerm
class (Monad m,Applicative m) => Sumbastiful m where
    getSumbastiBindings :: m Bindings
    putSumbastiBindings :: Bindings -> m ()
    setSumbasti :: SumtiAtom -> JboTerm -> m ()
    setSumbasti a t = (Map.insert a t <$> getSumbastiBindings) >>= putSumbastiBindings
    getSumbasti :: SumtiAtom -> m JboTerm
    getSumbasti a = (`getBinding` a) <$> getSumbastiBindings
instance Sumbastiful BridiM where
    getSumbastiBindings = sumbastiBindings <$> getParseState
    putSumbastiBindings bs = modifyParseState $ \ps -> ps{sumbastiBindings=bs}

getBinding :: Bindings -> SumtiAtom -> JboTerm
getBinding bs v =
    case Map.lookup v bs of
      Just o -> o
      Nothing -> case v of
		      (Assignable n) -> UnboundAssignable n
		      (LerfuString s) -> UnboundLerfuString s
		      _ -> error $ show v ++ " not bound.\n"

shuntVars :: (Int -> SumtiAtom) -> Bindings -> Bindings
shuntVars var bs = foldr ( \n -> Map.insert (var $ n+1)
					    (fromJust $ Map.lookup (var n) bs) )
			 bs
			 [ 1 .. head [ n-1 | n <- [1..],
				    isNothing $ Map.lookup (var n) bs ] ]

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
instance Varpool BridiM where
    getNextFresh = nextFreshVar <$> getParseState
    putNextFresh n = modifyParseState $ \ps -> ps{nextFreshVar=n}
    getReferenced = referencedVars <$> getParseState
    putReferenced rv = modifyParseState $ \ps -> ps{referencedVars=rv}

data Arglist = Arglist {args :: Args, position::Int}
type Args = Map ArgPos JboTerm
data ArgPos = NPos Int | JaiPos | BaiPos String
    deriving (Eq, Show, Ord)
class (Monad m,Applicative m) => Arglistful m where
    getArglist :: m Arglist
    putArglist :: Arglist -> m ()
    modifyArglist :: (Arglist -> Arglist) -> m ()
    modifyArglist f = (f <$> getArglist) >>= putArglist
instance Arglistful BridiM where
    getArglist = arglist <$> get
    putArglist al = modify $ \s -> s{arglist=al}

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
argsToJboterms as = map (\n -> Map.findWithDefault ZoheTerm (NPos n) as) [1..max] where
    max = maximum $ 1:[n | NPos n <- Map.keys as]

swapTerms :: [JboTerm] -> Int -> Int -> [JboTerm]
swapTerms ts n m = take (max (max n m) (length ts)) $
	swap (ts ++ (repeat ZoheTerm)) (n-1) (m-1)

-- | addImplicit: adds a jboterm at first empty positional slot
addImplicit :: JboTerm -> BridiM ()
addImplicit o = modifyArglist $ \al ->
    let as = args al
	gap = head $ [1..] \\ [n | NPos n <- Map.keys as]
    in al{args=(Map.insert (NPos gap) o as)}

data Arg = Arg Tag JboTerm
addArg :: Arg -> BridiM ()
addArg arg@(Arg tag o) = modifyArglist $
	(appendToArglist o) .
	(\as -> case tag of
	    Untagged -> as
	    FA n -> as{position=n})

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
instance VarBindful BridiM where
    getVarBindings = varBindings <$> get
    putVarBindings vbs = modify $ \s -> s{varBindings=vbs}

type Bridi = Args -> JboProp


mapProp :: (JboProp -> JboProp) -> BridiM ()
mapProp f = lift $ ContT $ \k -> f <$> k ()

-- |mapBridiM2 f m1 m2: fork, doing m1 and m2 then joining final Props with f;
--  ParseState threaded through as m1 then m2 then continuation.
mapBridiM2 :: (JboProp -> JboProp -> JboProp) -> BridiM a -> BridiM a -> BridiM a
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

partiallyResolveBridi :: (Bridi,BridiParseState) -> Bridi
partiallyResolveBridi (b,s) =
    \extraArgs -> b $ joinArgs (args $ arglist s) extraArgs
resolveBridi :: (Bridi,BridiParseState) -> JboProp
resolveBridi (b,s) = partiallyResolveBridi (b,s) nullArgs

runSubBridiM :: BridiM Bridi -> BridiM JboProp
runSubBridiM m = do
    s <- get
    putArglist nullArglist
    p <- lift.lift $ (`runContT` return.resolveBridi) $ (`runStateT` s) $ m
    return $ p

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
