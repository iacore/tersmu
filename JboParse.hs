module JboParse where

import FOL hiding (Term,Connective)
import JboProp
import JboSyntax
import BridiM

import Data.Maybe
import Data.Traversable (traverse)
import Control.Monad
import Control.Applicative
import Data.List

evalText :: [Statement] -> [JboProp]
evalText ss =
    evalParseStateM $ concat <$> mapM evalStatement ss

evalStatement :: Statement -> ParseStateM [JboProp]
evalStatement s = do
    p <- evalParseM (parseStatement s) >>= doQuestions True
    ps <- takeSideSentence
    return $ ps ++ [p]

data FreeReturn
    = FRSides [JboProp]
    | FRTruthQ (Maybe Int)
    | FRIgnored
evalFree :: Free -> ParseStateM FreeReturn
evalFree (Discursive bt) =
    (FRSides . (\p -> [p]) <$>) $ evalParseM $
	($nullArgs) <$> partiallyRunBridiM (parseBTail bt)
evalFree (Bracketed sts) =
    FRSides . concat <$> mapM evalStatement sts
evalFree (TruthQ kau) = return $ FRTruthQ kau
evalFree _ = return FRIgnored

doFrees :: [FreeIndex] -> ParseM r ()
doFrees = mapM_ doFree
doFree :: FreeIndex -> ParseM r ()
doFree fi = do
    f <- lookupFree fi
    fr <- liftParseStateMToParseM $ evalFree f
    case fr of
	FRSides ps -> mapM_ addSideSentence ps
	FRTruthQ kau -> addQuestion $ Question kau QTruth
	FRIgnored -> return ()

parseStatements :: [Statement] -> JboPropM JboProp
parseStatements ss = bigAnd <$> mapM parseStatement ss

parseStatement :: Statement -> JboPropM JboProp
parseStatement (Statement fs ps s) = do
    doFrees fs
    ignoringArgs $ parseTerms ps
    parseStatement1 s

parseStatement1 :: Statement1 -> JboPropM JboProp
parseStatement1 (ConnectedStatement con s1 s2) =
    doConnective False con (parseStatement1 s1) (parseStatement1 s2)
parseStatement1 (StatementStatements ss) =
    parseStatements ss
parseStatement1 (StatementSentence s) = do
    b <- partiallyRunBridiM $ parseSentence s
    modifyBribastiBindings $ setShunting (TUGOhA "go'i") b
    return $ b nullArgs

parseSubsentence :: Subsentence -> BridiM Bridi
parseSubsentence (Subsentence fs ps s) = do
    doFrees fs
    ignoringArgs $ parseTerms ps
    parseSentence s

parseSentence :: Sentence -> BridiM Bridi
parseSentence (Sentence ts bt) =
    parseTerms ts >> parseBTail bt

parseBTail :: BridiTail -> BridiM Bridi
parseBTail (GekSentence (ConnectedGS con ss1 ss2 tts)) =
    doConnective True con (parseSubsentence ss1) (parseSubsentence ss2)
	<* parseTerms tts

parseBTail (GekSentence (NegatedGS gs)) =
    mapProp Not >> parseBTail (GekSentence gs)

parseBTail (ConnectedBT con bt1 bt2 tts) =
    parseBTail (GekSentence (ConnectedGS con
	(Subsentence [] [] (Sentence [] bt1))
	(Subsentence [] [] (Sentence [] bt2)) tts))

parseBTail (BridiTail3 (Negated sb) tts) =
    -- XXX: need to handle Negated and tags here as well as in parseSelbri,
    -- because of the SBInverted handling within parseBTail below.
    mapProp Not >> parseBTail (BridiTail3 sb tts)
parseBTail (BridiTail3 (TaggedSelbri tag sb) tts) = do
    tag' <- parseTag tag
    doBareTag tag'
    parseBTail (BridiTail3 sb tts)

parseBTail (BridiTail3 (Selbri2 (SBInverted sb sb')) tts) =
    getInvertedRel sb sb' where
    getInvertedRel sb sb' =
	(parseSelbri3 sb >>=) $ applySeltau $ case sb' of
	    SBInverted sb'' sb''' -> getInvertedRel sb'' sb'''
	    Selbri3 sb'' -> parseSelbri $ Selbri2 (Selbri3 (TanruUnit (TUSelbri3 sb'') tts))

parseBTail (BridiTail3 sb tts) = do
    parseSelbri sb <* parseTerms tts

parseSelbri :: Selbri -> BridiM Bridi
parseSelbri (Negated sb) =
    mapProp Not >> parseSelbri sb
parseSelbri (TaggedSelbri tag sb) = do
    tag' <- parseTag tag
    doBareTag tag'
    parseSelbri sb
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
parseSelbri3 (ConnectedSB fore con sb sb') = do
    (con',p,p') <- if fore then do
	    con' <- parseConnective con
	    p <- selbriToPred sb
	    p' <- selbriToPred $ sb3tosb sb'
	    return (con',p,p')
	else do
	    p <- selbriToPred sb
	    con' <- parseConnective con
	    p' <- selbriToPred $ sb3tosb sb'
	    return (con',p,p')
    return $ jboRelToBridi $ TanruConnective con' p p'
parseSelbri3 (TanruUnit tu2 las) =
    advanceArgPosToBridi >> parseTU tu2 <* parseTerms las
parseSelbri3 (BridiBinding tu tu') = do
    case tu' of
	TanruUnit (TUBrivla bv) [] ->
	    if bv `elem` map (\v -> "brod" ++ [v]) "aeiou"
		then setBribastiToCurrent $ TUBrivla bv
		else return ()
	_ -> return ()
    parseSelbri3 tu

parseTU :: TanruUnit -> BridiM Bridi
parseTU (TUBrivla bv) = getBribasti $ TUBrivla bv
parseTU (TUGOhA "du" _) = return $ jboRelToBridi Equal
parseTU tu@(TUGOhA _ _) = getBribasti tu
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
	    pred <- subsentToPred ss rv >>= doQuestionsPred False
	    return $ jboRelToBridi $ AbsPred a pred
	Nothing -> jboRelToBridi . AbsProp a <$>
	    (runSubBridiM (parseSubsentence ss) >>= doQuestions False)
parseTU (TUPermuted n tu) =
    (.swapArgs (NPos 1) (NPos n)) <$> parseTU tu
parseTU (TUJai (Just tag) tu) = do
    tag' <- parseTag tag
    (.swapArgs (NPos 1) JaiPos) . withJaiAsTag tag' <$> parseTU tu
parseTU (TUJai Nothing tu) =
    (.swapArgs (NPos 1) JaiPos) . withJaiAsRaising <$> parseTU tu
parseTU (TUSelbri3 sb) = parseSelbri3 sb


parseTerms :: PreProp r => [Term] -> ParseM r ()
parseTerms = mapM_ parseTerm

parseTerm :: PreProp r => Term -> ParseM r (Maybe JboTerm)
parseTerm t = case t of
    Termset ts -> mapM_ parseTerm ts >> return Nothing
    ConnectedTerms fore con t1 t2 -> do
	doConnective fore con
	    (parseTerm t1)
	    (parseTerm t2)
	return Nothing
    Negation -> mapProp Not >> return Nothing
    Sumti (Tagged tag) s -> do
	tag' <- parseTag tag
	o <- parseSumti s
	doTag tag' (Just o)
	return Nothing
    Sumti taggedness s -> do
	o <- parseSumti s
	addArg $ Arg taggedness o
	return $ Just o
    BareFA (Just n) -> setArgPos n >> return Nothing
    BareFA Nothing -> return Nothing
    BareTag tag -> do
	tag' <- parseTag tag
	doBareTag tag'
	return Nothing

parseSumti :: PreProp r => Sumti -> ParseM r JboTerm
parseSumti s = do
    (o,ips,as) <- case s of
	(ConnectedSumti fore con s1 s2 rels) -> do
	    o <- case con of
		JboConnLog _ lcon -> do
		    o <- getFreshVar
		    {-
		    mapProp $ \p ->
			connToFOL lcon
			(subTerm o o1 p)
			(subTerm o o2 p)
		    -}
		    doConnective fore con 
			(do {o1 <- parseSumti s1; mapProp $ \p -> subTerm o o1 p})
			(do {o2 <- parseSumti s2; mapProp $ \p -> subTerm o o2 p})
		    return o
		JboConnJoik mtag joik -> do
		    when (isJust mtag) $ warning
			"Ignoring tag on non-logically connected sumti"
		    [o1,o2] <- mapM parseSumti [s1,s2]
		    return $ JoikedTerms joik o1 o2
	    (_,ips,as) <- parseRels rels
	    return (o,ips,as)
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
    o <- doAssigns o as
    -- |TODO: make this an option?
    -- o <- bindUnbound o
    updateReferenced o
    doIncidentals o ips
    return o
    where
	bindUnbound o@(UnboundSumbasti (MainBridiSumbasti _)) = return o
	bindUnbound o@(UnboundSumbasti _) = assignFreshConstant o
	bindUnbound o = return o
	assignFreshConstant o = do
	    o' <- getFreshConstant
	    doAssigns o [Right o']
	    return o'

type ParsedRels = ([JboPred],[JboPred],[Either SumtiAtom JboTerm])
parseRels :: PreProp r => [RelClause] -> ParseM r ParsedRels
parseRels [] = return ([],[],[])
parseRels (r:rs) = do
    (rps,ips,as) <- case r of
	Restrictive ss -> do
	    rp <- subsentToPred ss RelVar
	    return ([rp],[],[])
	Incidental ss -> do
	    ip <- subsentToPred ss RelVar >>= doQuestionsPred True
	    return ([],[ip],[])
	RestrictiveGOI goi t -> do
	    -- TODO: semantics of {pe BAI} etc
	    mo <- ignoringArgs $ parseTerm t
	    case mo of
		Nothing -> return ([],[],[])
		Just o ->
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
		    in return ([rp],[],[])
	IncidentalGOI goi t -> do
	    mo <- ignoringArgs $ parseTerm t
	    case mo of
		Nothing -> return ([],[],[])
		Just o ->
		    let rel = case goi of
			    "ne" -> Brivla "srana"
			    "no'u" -> Brivla "du"
			ip = \x -> Rel rel [x,o]
		    in return ([],[ip],[])
	Assignment (Sumti Untagged (QAtom Nothing [] sa)) | isAssignable sa -> 
	    return ([],[],[Left sa])
	Assignment t -> do
	    mo <- ignoringArgs $ parseTerm t
	    return ([],[], maybeToList $ Right <$> mo)
    (rps',ips',as') <- parseRels rs
    return (rps++rps',ips++ips',as++as')

parseVariable :: PreProp r => SumtiAtom -> [JboPred] -> Maybe Quantifier -> ParseM r JboTerm
parseVariable sa@(Variable n) rps mq = do
    x <- lookupVarBinding sa
    case (x,mq) of
	 (Just o,Nothing) -> return o
	 _ -> do
	    o <- quantify (fromMaybe Exists mq) $ andMPred rps
	    setVarBinding sa o
	    return o

parseSumtiAtom :: PreProp r => SumtiAtom -> ParseM r (JboTerm, ParsedRels)
parseSumtiAtom sa = do
    (rps,ips,as) <- case sa of
	Description _ mis _ _ rels _ ->
	    let rels' = rels
		    ++ case mis of
			Nothing -> []
			Just is -> [IncidentalGOI "ne" (Sumti Untagged is)]
	    in parseRels rels'
	QualifiedSumti _ rels _ -> parseRels rels
	Name rels _ ->
	    -- XXX: this construction, LA relativeClauses CMENE, appears not
	    -- to be mentioned in CLL; an alternative plausible semantics
	    -- would be that the relative clauses become "part of the name",
	    -- as with inner relative clauses in LA description sumti.
	    parseRels rels
	_ -> return ([],[],[])
    o <- case sa of
	Description gadri _ miq sb _ irels -> do
	    -- TODO: gadri other than {lo}
	    sr <- selbriToPred sb
	    (irps,iips,ias) <- parseRels irels
	    let xorlo_ips = sr : 
		       (case miq of
			 Just iq -> [(\o -> Rel (Moi iq "mei") [o])]
			 _ -> []) ++
		       iips
	    o <- getFreshConstant
	    doAssigns o ias
	    doIncidentals o xorlo_ips
	    return o
	QualifiedSumti qual _ s -> do
	    o <- parseSumti s
	    return $ QualifiedTerm qual o
	RelVar _ -> getVarBinding sa
	LambdaVar _ -> getVarBinding sa
	Ri _ -> getSumbasti sa
	Assignable _ -> getSumbasti sa
	LerfuString _ -> getSumbasti sa
	MainBridiSumbasti _ -> getSumbasti sa
	SumtiQ kau -> addSumtiQuestion kau
	Zohe -> getFreshConstant
	-- TODO: following ought all to give fresh constants, really
	NonAnaphoricProsumti ps -> return $ NonAnaph ps
	Name _ s -> return $ Named s
	Quote sts ->
	    -- TODO: quotes shouldn't have access to higher level bindings
	    -- TODO: should probably return the unparsed text as well?
	    JboQuote . ParsedQuote . concat <$>
		(liftParseStateMToParseM $ mapM evalStatement sts)
	ErrorQuote vs -> return $ JboErrorQuote vs
	NonJboQuote s -> return $ JboNonJboQuote s
	Word s -> return $ Valsi s
    updateSumbastiWithSumtiAtom sa o
    return (o,(rps,ips,as))

parseTag :: PreProp r => Tag -> ParseM r JboTag
parseTag (ConnectedTag con@(JboConnLog _ _) tag1 tag2) = do
    doConnective False con
	(parseTag tag1)
	(parseTag tag2)
parseTag (ConnectedTag joicon tag1 tag2) =
    ConnectedTag <$> parseConnective joicon <*> parseTag tag1 <*> parseTag tag2
parseTag (DecoratedTagUnits dtus) = (DecoratedTagUnits <$>) $
    (`mapM` dtus) $ \(DecoratedTagUnit nahe se nai u) ->
	DecoratedTagUnit nahe se nai <$> parseTagUnit u
parseTagUnit :: PreProp r => TagUnit -> ParseM r JboTagUnit
parseTagUnit (TenseCmavo c) = return $ TenseCmavo c
parseTagUnit (BAI c) = return $ BAI c
parseTagUnit (FAhA m c) = return $ FAhA m c
parseTagUnit (TAhE_ZAhO f c) = return $ TAhE_ZAhO f c
parseTagUnit (ROI f q) = ROI f <$> parseQuantifier q
parseTagUnit (FIhO selbri) = FIhO <$> selbriToPred selbri
parseTagUnit KI = error "TODO: ki"
parseTagUnit CUhE = error "TODO: cu'e"

parseConnective :: PreProp r => Connective -> ParseM r JboConnective
parseConnective (JboConnLog mtag lcon) = do
    mtag' <- traverse parseTag mtag
    return $ JboConnLog mtag' lcon
parseConnective (JboConnJoik mtag joik) = do
    mtag' <- traverse parseTag mtag
    return $ JboConnJoik mtag' joik

parseQuantifier :: PreProp r => Quantifier -> ParseM r Quantifier
parseQuantifier = return

quantify :: PreProp r => Quantifier -> Maybe JboPred -> ParseM r JboTerm
quantify q r = do
    fresh <- getFreshVar
    mapProp $ \p ->
	Quantified q (singpred <$> r) $
	    \v -> subTerm fresh (Var v) p
    return fresh
    where
	singpred r = \v -> r (Var v)

doTag :: PreProp r => JboTag -> Maybe JboTerm -> ParseM r ()
doTag (DecoratedTagUnits dtus) Nothing =
    -- separate into a stream of possibly negated modals
    -- (no obvious way to make sense of this with JOI connection,
    -- and doesn't fit current sumtcita handling)
    mapM_ doDTU dtus where
	doDTU dtu = do
	    when (tagNAI dtu) $ mapProp Not
	    doModal $ JboTagged (DecoratedTagUnits [dtu{tagNAI=False}]) Nothing
doTag jtag mt = doModal $ JboTagged jtag mt

doModal :: PreProp r => JboOperator -> ParseM r ()
doModal op = mapProp (Modal op)

doBareTag :: PreProp r => JboTag -> ParseM r ()
doBareTag tag = doTag tag Nothing

-- |applySeltau: operate on a Bridi with a seltau by tanruising every JboRel
-- in the JboProp.
applySeltau :: BridiM Bridi -> Bridi -> BridiM Bridi
applySeltau seltauM tertau = do
    stpred <- parsedSelbriToPred seltauM
    let f = terpProp (\r ts -> Rel (Tanru stpred r) ts) id
    return $ f . tertau 

selbriToPred :: Selbri -> ParseM r JboPred
selbriToPred sb = parsedSelbriToPred $ parseSelbri sb
parsedSelbriToPred :: BridiM Bridi -> ParseM r JboPred
parsedSelbriToPred m = do
    fresh <- getFreshVar
    p <- runSubBridiM $ m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> ParseM r JboPred
subsentToPred ss rv = do
    fresh@(PreVar n) <- getFreshVar
    p <- runSubBridiM $ do
	modifyVarBindings $ setShunting rv fresh
	p <- parseSubsentence ss
	reffed <- referenced n
	when (not reffed) $ addImplicit fresh
	return p
    return $ \o -> subTerm fresh o p

doConnective :: PreProp r => Bool -> Connective -> ParseM r a -> ParseM r a -> ParseM r a
doConnective isForethought con m1 m2 = do
    let (mtag,con') = case con of
	    JboConnLog mtag lcon -> (mtag, connToFOL lcon)
	    JboConnJoik mtag joik -> (mtag, joikToFOL joik)
    (m1',m2') <- case mtag of
	Nothing -> return $ (m1,m2)
	Just tag -> do
	    v <- quantify Exists Nothing
	    if isForethought then do
		    tag' <- parseTag tag
		    return $ (doModal (WithEventAs v) >> m1
			, (doTag tag' $ Just v) >> m2)
		else if isTense tag
		    then return $ (doModal (WithEventAs v) >> m1
			    , parseTag tag >>= (`doTag` Just v) >> m2)
		    else return $ ( (parseTag tag >>= (`doTag` Just v)) >> m1
			    , doModal (WithEventAs v) >> m2)
    mapParseM2 con' m1' m2'

-- TODO
warning = error
