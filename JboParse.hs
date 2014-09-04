module JboParse where

import FOL hiding (Term,Connective)
import JboProp
import JboSyntax
import BridiM
import Util

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
parseSelbri3 (ScalarNegatedSB nahe sb) =
    mapRelsInBridi (ScalarNegatedRel nahe) <$> parseSelbri3 sb
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
parseTU (TUMoi q m) = do
    jq <- evalMex q
    return $ jboRelToBridi $ Moi jq m
parseTU (TUAbstraction (NegatedAbstractor a) ss) =
    mapProp Not >> parseTU (TUAbstraction a ss)
parseTU (TUAbstraction (LogConnectedAbstractor lcon a1 a2) ss) =
    doConnective False (JboConnLog Nothing lcon)
	(parseTU $ TUAbstraction a1 ss)
	(parseTU $ TUAbstraction a2 ss)
parseTU (TUAbstraction a ss) =
    case
	case a of
	    NU "poi'i" ->
		 -- poi'i: an experimental NU, which takes ke'a rather
		 -- than ce'u; {ko'a poi'i ke'a broda} means
		 -- {ko'a broda}. See http://www.lojban.org/tiki/poi'i
		 Just RelVar
	    NU "ka" -> Just LambdaVar
	    NU "ni" -> Just LambdaVar
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
parseTU (TUXOhI tag) = do
    -- xo'i: experimental cmavo which extracts the underlying binary relation
    -- from a tag; essentially an inverse to fi'o. Proposed by selpa'i.
    -- Necessary for handling e.g. the {ne BAI} construction.
    jbotag <- parseTag tag
    return $ jboRelToBridi $ TagRel jbotag
parseTU (TUSelbri3 sb) = parseSelbri3 sb


parseTerms :: PreProp r => [Term] -> ParseM r ()
parseTerms = mapM_ (\t -> do
	ret <- parseTerm t
	case ret of
	    Just (Left (jbotag,mo)) -> doTag jbotag mo
	    _ -> return ())

parseTerm :: PreProp r => Term -> ParseM r (Maybe (Either (JboTag, Maybe JboTerm) JboTerm))
parseTerm t = case t of
    Termset ts -> mapM_ parseTerm ts >> return Nothing
    ConnectedTerms fore con t1 t2 -> do
	doConnective fore con
	    (parseTerm t1)
	    (parseTerm t2)
	return Nothing
    Negation -> mapProp Not >> return Nothing
    Sumti (Tagged tag) s -> do
	jbotag <- parseTag tag
	o <- parseSumti s
	return $ Just $ Left (jbotag, Just o)
    Sumti taggedness s -> do
	o <- parseSumti s
	addArg $ Arg taggedness o
	return $ Just $ Right o
    BareFA (Just n) -> setArgPos n >> return Nothing
    BareFA Nothing -> return Nothing
    BareTag tag -> (\jt -> Just $ Left (jt, Nothing)) <$> parseTag tag

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
		mjq <- traverse evalMex mq
		(rps,ips,as) <- parseRels rels
		o <- parseVariable sa rps mjq
		return (o,ips,as)
	     _ -> do
		 mjq <- traverse evalMex mq
		 (o,(rps,ips,as)) <- parseSumtiAtom sa
		 (rps',ips',as') <- parseRels rels
		 o' <- case mjq of
		   Nothing -> return o
		   Just jq -> do
		    quantify jq $ andMPred $ (isAmong o):(rps++rps')
		 return (o',ips++ips',as++as')
	(QSelbri q rels sb) -> do
	    jq <- evalMex q
	    sr <- selbriToPred sb
	    (rps,ips,as) <- parseRels rels
	    o <- quantify jq (andMPred $ sr:rps)
	    return (o,ips,as)
    o <- doIncidentals o ips
    o <- doAssigns o as
    -- |TODO: make this an option?
    -- o <- bindUnbound o
    updateReferenced o
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
	RestrictiveGOI goi t -> goiRels goi True t
	IncidentalGOI goi t -> goiRels goi False t
	Assignment (Sumti Untagged (QAtom Nothing [] sa)) | isAssignable sa -> 
	    return ([],[],[Left sa])
	Assignment t -> do
	    ret <- ignoringArgs $ parseTerm t
	    case ret of
		Just (Right o) -> return ([],[], [Right o])
		_ -> return ([],[],[])
    (rps',ips',as') <- parseRels rs
    return (rps++rps',ips++ips',as++as')
    where
	goiRels goi restrictive t = do
	    ret <- ignoringArgs $ parseTerm t
	    let ps = maybeToList $ case ret of
		    Just (Right o) ->
			let rel = case goi of
				"pe" -> Brivla "srana"
				"ne" -> Brivla "srana"
				"po'u" -> Brivla "du"
				"no'u" -> Brivla "du"
				-- XXX: following are rather approximate... the
				-- BPFK subordinators section suggests more
				-- complicated expressions
				"po'e" -> Tanru (\o -> Rel (Brivla "jinzi") [o])
					    (Brivla "srana")
				"po" -> Tanru (\o -> Rel (Brivla "steci") [o])
					    (Brivla "srana")
			in Just $ \x -> Rel rel [x,o]
		    Just (Left (jbotag, mo)) -> Just $ \x -> Rel (TagRel jbotag) [fromMaybe ZoheTerm mo,x]
		    _ -> Nothing
	    return $ if restrictive then (ps,[],[]) else ([],ps,[])

parseVariable :: PreProp r => SumtiAtom -> [JboPred] -> Maybe Value -> ParseM r JboTerm
parseVariable sa@(Variable n) rps mjq = do
    x <- lookupVarBinding sa
    case (x,mjq) of
	 (Just o,Nothing) -> return o
	 _ -> do
	    o <- quantify (fromMaybe (Quantifier Exists) mjq) $ andMPred rps
	    setVarBinding sa o
	    return o

parseSumtiAtom :: PreProp r => SumtiAtom -> ParseM r (JboTerm, ParsedRels)
parseSumtiAtom sa = do
    (rps,ips,as) <- case sa of
	Description _ _ _ _ rels _ -> parseRels rels
	QualifiedSumti _ rels _ -> parseRels rels
	Name rels _ ->
	    -- XXX: this construction, LA relativeClauses CMENE, appears not
	    -- to be mentioned in CLL; an alternative plausible semantics
	    -- would be that the relative clauses become "part of the name",
	    -- as with inner relative clauses in LA description sumti.
	    parseRels rels
	_ -> return ([],[],[])
    o <- case sa of
	Description gadri mis miq sb _ irels -> do
	    -- TODO: gadri other than {lo}
	    mjq <- traverse evalMex miq
	    sr <- selbriToPred sb
	    (irps,iips,ias) <- parseRels $
		irels ++ maybeToList ((\is ->
		    IncidentalGOI "ne" (Sumti Untagged is)) <$> mis)
	    let xorlo_ips = sr : 
		    (case mjq of
			Just jq -> [(\o -> Rel (Moi jq "mei") [o])]
			_ -> [])
		    ++ iips
	    o <- getFreshConstant
	    o <- doIncidentals o xorlo_ips
	    doAssigns o ias
	    return o
	QualifiedSumti qual _ s -> do
	    o <- parseSumti s
	    return $ QualifiedTerm qual o
	MexLi m -> Value <$> evalMex m
	MexMex m -> return $ TheMex m
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
parseTagUnit (ROI f q) = ROI f <$> parseMex q
parseTagUnit (FIhO sb) = FIhO <$> selbriToPred sb
-- XXX: for now at least, we just pass through ki as if it were a normal tag
-- (this is what the BPFK section suggests at the time of writing:
-- ki == fi'o manri, with all the complexity of CLL's ki presumably being
-- considered merely usage conventions. I'm not very happy with this, but nor
-- do I see a neat way to formalise those conventions, so this will have to do
-- for now.
parseTagUnit KI = return KI
-- TODO: we should actually deal with cu'e, though
parseTagUnit CUhE = return CUhE

parseConnective :: PreProp r => Connective -> ParseM r JboConnective
parseConnective (JboConnLog mtag lcon) = do
    mtag' <- traverse parseTag mtag
    return $ JboConnLog mtag' lcon
parseConnective (JboConnJoik mtag joik) = do
    mtag' <- traverse parseTag mtag
    return $ JboConnJoik mtag' joik

evalMex :: PreProp r => Mex -> ParseM r Value
evalMex m = MexValue <$> parseMex m

parseMex :: PreProp r => Mex -> ParseM r JboMex
parseMex m = reduceMex <$> parseMex' m where
    parseMex' (ConnectedMex fore con@(JboConnLog _ _) m1 m2) = do
	doConnective fore con
	    (parseMex' m1)
	    (parseMex' m2)
    parseMex' (ConnectedMex fore con@(JboConnJoik _ _) m1 m2) =
	ConnectedMex fore <$> parseConnective con <*> parseMex' m1 <*> parseMex' m2
    parseMex' (Operation op ms) = Operation <$> parseOperator op <*> mapM parseMex' ms
    parseMex' (MexArray ms) = MexArray <$> mapM parseMex' ms
    parseMex' (QualifiedMex q m) = QualifiedMex q <$> parseMex' m
    parseMex' (MexSelbri sb) = MexSelbri <$> selbriToPred sb
    parseMex' (MexSumti s) = MexSumti <$> parseSumti s
    parseMex' (MexInt n) = return $ MexInt n
    parseMex' (MexNumeralString ns) = return $ MexNumeralString ns
    parseMex' (MexLerfuString ls) = return $ MexLerfuString ls
    parseOperator :: PreProp r => Operator -> ParseM r JboOperator
    parseOperator (ConnectedOperator fore con@(JboConnLog _ _) o1 o2) = do
	doConnective fore con
	    (parseOperator o1)
	    (parseOperator o2)
    parseOperator (ConnectedOperator fore con@(JboConnJoik _ _) o1 o2) =
	ConnectedOperator fore <$> parseConnective con <*> parseOperator o1 <*> parseOperator o2
    parseOperator (OpPermuted s o) = OpPermuted s <$> parseOperator o
    parseOperator (OpScalarNegated n op) = OpScalarNegated n <$> parseOperator op
    parseOperator (OpMex m) = OpMex <$> parseMex' m
    parseOperator (OpSelbri sb) = OpSelbri <$> selbriToPred sb
    parseOperator (OpVUhU v) = return $ OpVUhU v
    reduceMex :: JboMex -> JboMex
    reduceMex (Operation op ms) = applyJboOperator op ms
    reduceMex m = m
    nullMex = MexNumeralString [PA "tu'o"]
    nullOp = OpVUhU "ge'a"
    stripNulls :: [JboMex] -> [JboMex]
    stripNulls (Operation nullop os:os') | nullop == nullOp =
	stripNulls os ++ stripNulls os'
    stripNulls (nullo:os) | nullo == nullMex = stripNulls os
    stripNulls (o:os) = o : stripNulls os
    stripNulls [] = []
    applyJboOperator :: JboOperator -> [JboMex] -> JboMex
    applyJboOperator (OpPermuted s op) os =
	applyJboOperator op $ swapFiniteWithDefault nullMex (stripNulls os) 0 $ s-1
    applyJboOperator nullop (Operation op os:os') | nullop == nullOp =
	applyJboOperator op $ os++os'
    applyJboOperator op os = Operation op $ stripNulls os

quantify :: PreProp r => Value -> Maybe JboPred -> ParseM r JboTerm
quantify jq r = do
    fresh <- getFreshVar
    mapProp $ \p ->
	Quantified (ValueQuantifier jq) (singpred <$> r) $
	    \v -> subTerm fresh (BoundVar v) p
    return fresh
    where
	singpred r = \v -> r (BoundVar v)

doTag :: PreProp r => JboTag -> Maybe JboTerm -> ParseM r ()
doTag (DecoratedTagUnits dtus) Nothing =
    -- separate into a stream of possibly negated modals
    -- (no obvious way to make sense of this with JOI connection,
    -- and doesn't fit current sumtcita handling)
    mapM_ doDTU dtus where
	doDTU dtu = do
	    -- TODO FIXME: TAhE, ROI, ZAhE, and (in ZG) CAhA have scalar nai
	    when (tagNAI dtu) $ mapProp Not
	    doModal $ JboTagged (DecoratedTagUnits [dtu{tagNAI=False}]) Nothing
doTag jtag mt = doModal $ JboTagged jtag mt

doModal :: PreProp r => JboModalOp -> ParseM r ()
doModal op = mapProp (Modal op)

doBareTag :: PreProp r => JboTag -> ParseM r ()
doBareTag tag = doTag tag Nothing

-- |applySeltau: operate on a Bridi with a seltau by tanruising every JboRel
-- in the JboProp.
-- XXX: not clear that this is correct in e.g.
-- {broda gi'e brode .i brodi go'i}, but not clear what is correct.
applySeltau :: BridiM Bridi -> Bridi -> BridiM Bridi
applySeltau seltauM tertau = do
    stpred <- parsedSelbriToPred seltauM
    return $ mapRelsInBridi (Tanru stpred) tertau
mapRelsInBridi :: (JboRel -> JboRel) -> Bridi -> Bridi
mapRelsInBridi f b = (terpProp (\r ts -> Rel (f r) ts) id id) . b

selbriToPred :: Selbri -> ParseM r JboPred
selbriToPred sb = parsedSelbriToPred $ parseSelbri sb
parsedSelbriToPred :: BridiM Bridi -> ParseM r JboPred
parsedSelbriToPred m = do
    fresh <- getFreshVar
    p <- runSubBridiM $ m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> ParseM r JboPred
subsentToPred ss rv = do
    fresh@(Var n) <- getFreshVar
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
	    v <- quantify (Quantifier Exists) Nothing
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
warning _ = return ()
