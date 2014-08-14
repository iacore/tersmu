module JboParse where

import FOL hiding (Term)
import JboProp
import JboSyntax
import BridiM

import Data.Maybe
import Control.Monad
import Control.Applicative
import Data.List

parseStatements :: [Statement] -> JboPropM JboProp
parseStatements ss = mapM parseStatement ss >>= return . bigAnd

parseStatement :: Statement -> JboPropM JboProp
parseStatement (Statement ps s) = do
    ignoringArgs $ parseTerms ps
    p <- parseStatement1 s
    ps <- takeSideSentence
    return $ bigAnd $ ps ++ [p]

parseStatement1 :: Statement1 -> JboPropM JboProp
parseStatement1 (ConnectedStatement con s1 s2) =
    do p1 <- parseStatement1 s1
       p2 <- parseStatement1 s2
       return $ connToFOL con p1 p2
parseStatement1 (StatementStatements ss) =
    parseStatements ss
parseStatement1 (StatementSentence s) = do
    b <- partiallyRunBridiM $ parseSentence s
    setBribasti "go'i" b
    return $ b nullArgs

parseSubsentence :: Subsentence -> BridiM Bridi
parseSubsentence (Subsentence ps s) = do
    ignoringArgs $ parseTerms ps
    parseSentence s


parseSentence :: Sentence -> BridiM Bridi
parseSentence (Sentence ts bt) =
    parseTerms ts >> parseBTail bt

parseBTail :: BridiTail -> BridiM Bridi
parseBTail (GekSentence (ConnectedGS con ss1 ss2 tts)) =
    mapParseM2 (connToFOL con) (parseSubsentence ss1) (parseSubsentence ss2)
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
    getInvertedRel sb sb' where
    getInvertedRel sb sb' =
	(parseSelbri3 sb >>=) $ applySeltau $ case sb' of
	    SBInverted sb'' sb''' -> getInvertedRel sb'' sb'''
	    Selbri3 sb'' -> parseSelbri $ Selbri2 (Selbri3 (TanruUnit (TUSelbri3 sb'') tts))

parseBTail (BridiTail3 sb tts) = do
    advanceArgPosToBridi
    parseSelbri sb <* parseTerms tts

parseSelbri :: Selbri -> BridiM Bridi
parseSelbri (Negated sb) =
    mapProp Not >> parseSelbri sb
parseSelbri (Selbri2 sb) =
    parseSelbri2 sb

parseSelbri2 :: Selbri2 -> BridiM Bridi
parseSelbri2 (SBInverted sb sb') = do
    -- XXX: this works correctly only when there are no tailterms; see
    -- parseBTail above for tailterm handling.
    parseSelbri3 sb >>= applySeltau (parseSelbri2 sb')

parseSelbri2 (Selbri3 sb) =
    parseSelbri3 sb

parseSelbri3 :: Selbri3 -> BridiM Bridi
parseSelbri3 (SBTanru sb sb') = do
    applySeltau (parseSelbri3 sb) =<< parseSelbri3 sb'
parseSelbri3 (ConnectedSB con sb sb') =
    -- XXX: CLL arguably prescribes handling logical connections like
    -- non-logical connections here, with indeterminate semantics; but we
    -- handle them like giheks.
    -- Note that in any case, non-logical connections mean that we can't
    -- actually eliminate the ConnectedRels or PermutedRel constructors
    -- (consider {se broda joi brode})
    mapParseM2 (connToFOL con) (parseSelbri3 sb) (parseSelbri3 sb')
parseSelbri3 (TanruUnit tu2 las) =
    parseTU tu2 <* parseTerms las
parseSelbri3 (BridiBinding tu tu') = do
    case tu' of
	TanruUnit (TUBrivla bv) [] ->
	    if bv `elem` map (\v -> "brod" ++ [v]) "aeiou"
		then setBribastiToCurrent bv
		else return ()
	_ -> return ()
    parseSelbri3 tu

parseTU :: TanruUnit2 -> BridiM Bridi
parseTU (TUBrivla bv) = getBribasti bv
parseTU (TUGOhA g) = getBribasti g
parseTU (TUMe s) = do
    o <- parseSumti s
    return $ jboRelToBridi $ Among o
parseTU (TUMoi q m) = return $ jboRelToBridi $ Moi q m
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
	    return $ jboRelToBridi $ AbsPred a pred
	Nothing -> jboRelToBridi . AbsProp a <$>
	    (runSubBridiM $ parseSubsentence ss)
parseTU (TUPermuted n tu) =
    (.swapArgs (NPos 1) (NPos n)) <$> parseTU tu
parseTU (TUSelbri3 sb) = parseSelbri3 sb


parseTerms :: PreProp r => [Term] -> ParseM r ()
parseTerms = mapM_ parseTerm

parseTerm :: PreProp r => Term -> ParseM r ()
parseTerm t = case t of
    Termset ts -> mapM_ parseTerm ts
    ConnectedTerms con t1 t2 ->
	mapParseM2 (connToFOL con)
	    (parseTerm t1)
	    (parseTerm t2)
    Negation -> mapProp Not
    Sumti tag s -> do 
	o <- parseSumti s
	addArg $ Arg tag o

parseSumti :: PreProp r => Sumti -> ParseM r JboTerm
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
	(QAtom mq rels sa) -> case sa of
	     Variable _ -> do
		(rps,ips,as) <- parseRels rels
		o <- parseVariable sa rps mq
		return (o,ips,as)
	     _ -> do
		 (o,(rps,ips,as)) <- parseSumtiAtom sa
		 (rps',ips',as') <- parseRels rels
		 o' <- case mq of
		   Nothing -> return o
		   Just q -> quantify q $ andMPred $ (isAmong o):(rps++rps')
		 return (o',ips++ips',as++as')
	(QSelbri q rels sb) -> do
	    sr <- selbriToPred sb
	    (rps,ips,as) <- parseRels rels
	    o <- quantify q (andMPred $ sr:rps)
	    return (o,ips,as)
    updateParseStateWithJboTerm o
    doAssigns o as
    doIncidentals o ips
    return o

type ParsedRels = ([JboPred],[JboPred],[SumtiAtom])
parseRels :: PreProp r => [RelClause] -> ParseM r ParsedRels
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
	    -- TODO: handle {ko'a goi lo broda}
	    return ([],[],[])
    (rps',ips',as') <- parseRels rs
    return (rps++rps',ips++ips',as++as')

isAssignable :: SumtiAtom -> Bool
isAssignable (Assignable _) = True
isAssignable (LerfuString _) = True
isAssignable (Name _) = True
isAssignable _ = False

parseVariable :: PreProp r => SumtiAtom -> [JboPred] -> Maybe Quantifier -> ParseM r JboTerm
parseVariable sa@(Variable n) rps mq = do
    x <- lookupVarBinding sa
    case x of
	 Nothing -> do
	    o <- quantify (fromMaybe Exists mq) $ andMPred rps
	    setVarBinding sa o
	    return o
	 Just o -> do
	    return o
parseSumtiAtom :: PreProp r => SumtiAtom -> ParseM r (JboTerm, ParsedRels)
parseSumtiAtom sa = do
    (rps,ips,as) <- case sa of
	Description _ mis _ _ rels _ ->
	    let rels' = rels
		    ++ case mis of
			Nothing -> []
			Just is -> [RestrictiveGOI "pe" is]
	    in parseRels rels'
	_ -> return ([],[],[])
    o <- case sa of
	Description gadri _ miq sb _ irels -> do
	    -- Below is a bastard combination of CLL and xorlo.
	    -- TODO: implement proper CLL rules, as an option.
	    -- TODO: also properly implement xorlo
	    sr <- selbriToPred sb
	    (irps,iips,ias) <- parseRels irels
	    let r = andPred $
		       (case miq of
			 Just iq -> [(\o -> Rel (Moi iq "mei") [o])]
			 _ -> []) ++
		       irps ++
		       [sr]
	    o <- quantify (Gadri gadri) (Just r)
	    doAssigns o ias
	    doIncidentals o iips
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
    return (o,(rps,ips,as))


quantify :: PreProp r => Quantifier -> Maybe JboPred -> ParseM r JboTerm
quantify q r = do
    fresh <- getFreshVar
    mapProp $ \p ->
	Quantified q (singpred <$> r) $
	    \v -> subTerm fresh (Var v) p
    return fresh
    where
	singpred r = \v -> r (Var v)

-- |applySeltau: operate on a Bridi with a seltau by tanruising every JboRel
-- in the JboProp.
applySeltau :: BridiM Bridi -> Bridi -> BridiM Bridi
applySeltau seltauM tertau = do
    stpred <- parsedSelbriToPred seltauM
    let f = terpProp (\r ts -> Rel (Tanru stpred r) ts)
    return $ f . tertau 

selbriToPred :: Selbri -> ParseM r JboPred
selbriToPred sb = do
    parsedSelbriToPred $ parseSelbri sb
parsedSelbriToPred :: BridiM Bridi -> ParseM r JboPred
parsedSelbriToPred m = do
    fresh <- getFreshVar
    p <- runSubBridiM $ m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> ParseM r JboPred
subsentToPred ss rv = do
    fresh@(Var n) <- getFreshVar
    p <- runSubBridiM $ do
	modifyVarBindings $ shuntVars rv
	setVarBinding (rv 1) fresh
	p <- parseSubsentence ss
	reffed <- referenced n
	when (not reffed) $ addImplicit fresh
	return p
    return $ \o -> subTerm fresh o p
