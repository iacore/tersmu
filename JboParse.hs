module JboParse where

import FOL hiding (Term,Connective)
import JboProp
import JboSyntax
import BridiM
import Util

import Data.Maybe
import Data.Either
import Data.Traversable (traverse)
import Control.Monad
import Control.Applicative
import Data.List

evalText :: Text -> ParseStateM JboText
evalText (Text fs nai paras) = do
	doFrees fs
	concat <$> mapM evalFragOrStatement (concat paras)
    where
	evalFragOrStatement (Left frag) = (\x->[x]) . TexticuleFrag <$> parseFrag frag
	evalFragOrStatement (Right st) = map TexticuleProp <$> evalStatement st

-- XXX: we don't handle fragments properly at all currently
-- (to be done as part of any eventual question-and-answer handling)
parseFrag :: Fragment -> ParseStateM JboFragment
parseFrag (FragTerms ts) = evalParseM $ JboFragTerms <$> parseTerms ts
parseFrag f = return $ JboFragUnparsed f

evalStatement :: Statement -> ParseStateM [JboProp]
evalStatement s = do
    p <- evalParseM (parseStatement s) >>= doQuestions True
    ps <- propTexticules <$> takeSideTexticules
    return $ ps ++ [p]

data FreeReturn
    = FRSides JboText
    | FRTruthQ (Maybe Int)
    | FRIgnored
evalFree :: Free -> ParseStateM FreeReturn
evalFree (Discursive bt) =
    (FRSides . (\p -> [TexticuleProp p]) <$>) $ evalParseM $
	($nullArgs) <$> partiallyRunBridiM (parseBTail bt)
evalFree (Bracketed text) = FRSides <$> evalText text
evalFree (TruthQ kau) = return $ FRTruthQ kau
evalFree _ = return FRIgnored

doFrees :: [Free] -> ParseStateM ()
doFrees = mapM_ doFree
doFreesInParseM :: [Free] -> ParseM r ()
doFreesInParseM = liftParseStateMToParseM . doFrees
doFree :: Free -> ParseStateM ()
doFree f = do
    fr <- evalFree f
    case fr of
	FRSides jt -> mapM_ addSideTexticule jt
	FRTruthQ kau -> addQuestion $ Question kau QTruth
	FRIgnored -> return ()

parseStatements :: [Statement] -> JboPropM JboProp
parseStatements ss = bigAnd <$> mapM parseStatement ss

parseStatement :: Statement -> JboPropM JboProp
parseStatement (Statement fs ps s) = do
    doFreesInParseM fs
    ignoringArgs $ parseTerms ps
    parseStatement1 s

parseStatement1 :: Statement1 -> JboPropM JboProp
parseStatement1 (ConnectedStatement con s1 s2) =
    doConnective False con (parseStatement1 s1) (parseStatement1 s2)
parseStatement1 (StatementParas ps) =
    -- TODO: ought to parse fragments here (if only to pick up assigns etc)
    parseStatements $ rights $ concat ps
parseStatement1 (StatementSentence fs s) = do
    doFreesInParseM fs
    b <- partiallyRunBridiM $ parseSentence s
    modifyBribastiBindings $ setShunting (TUGOhA "go'i") b
    return $ b nullArgs

parseSubsentence :: Subsentence -> BridiM Bridi
parseSubsentence (Subsentence fs ps s) = do
    doFreesInParseM fs
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

parseBTail (GekSentence (TaggedGS tag gs)) = do
    tag' <- parseTag tag
    doBareTag tag'
    parseBTail (GekSentence gs)

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
parseTU (TUMoi s moi) = do
    o <- parseSumti s
    return $ jboRelToBridi $ Moi o moi
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
parseTU (TUOperator op) = do
    jboRelToBridi . OperatorRel <$> parseOperator op
parseTU (TUXOhI tag) = do
    -- xo'i: experimental cmavo which extracts the underlying binary relation
    -- from a tag; essentially an inverse to fi'o. Proposed by selpa'i.
    -- Necessary for handling e.g. the {ne BAI} construction.
    jbotag <- parseTag tag
    return $ jboRelToBridi $ TagRel jbotag
parseTU (TUSelbri3 sb) = parseSelbri3 sb


parseTerms :: PreProp r => [Term] -> ParseM r [JboTerm]
parseTerms ts = concat <$> flip mapM ts (\t -> do
	ret <- parseTerm t
	case ret of
	    Just (Left (jbotag,mo)) -> doTag jbotag mo >> return []
	    Just (Right o) -> return [o]
	    _ -> return [])

parseTerm :: PreProp r => Term -> ParseM r (Maybe (Either (JboTag, Maybe JboTerm) JboTerm))
parseTerm (Term fs mt) = 
    join <$> traverse parseTerm' mt <* doFreesInParseM fs
parseTerm' t = case t of
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
    (o,jrels) <- case s of
	(ConnectedSumti fore con s1 s2 rels) -> do
	    o <- case con of
		JboConnLog _ lcon -> do
		    o <- getFreshVar $ UnrestrictedDomain
		    doConnective fore con 
			(do o1 <- parseSumti s1
			    mapProp $ \p -> subTerm o o1 p
			    setDomain o $ FiniteDomain [o1])
			(do o2 <- parseSumti s2
			    mapProp $ \p -> subTerm o o2 p
			    modifyDomain o $ \(FiniteDomain [o1]) -> FiniteDomain [o1,o2])
		    return o
		JboConnJoik mtag joik -> do
		    when (isJust mtag) $ warning
			"Ignoring tag on non-logically connected sumti"
		    [o1,o2] <- mapM parseSumti [s1,s2]
		    return $ JoikedTerms joik o1 o2
	    jrels <- parseRels rels
	    return (o,jrels)
	(QAtom mq rels sa) -> case sa of
	     Variable _ -> do
		mm <- traverse parseMex mq
		(rps,jrels) <- stripForeRestrictives <$> parseRels rels
		o <- parseVariable sa rps mm
		return (o,jrels)
	     _ -> do
		 mm <- traverse parseMex mq
		 (o,ijrels) <- parseSumtiAtom sa
		 jrels <- (ijrels++) <$> parseRels rels
		 (o,jrels) <- case mm of
		     Nothing -> return (o,jrels)
		     Just m | m == nullMex ->
			-- tu'o as a sumti quantifier acts like no quantifier
			return (o,jrels)
		     Just m -> do
			let (rps,jrels') = stripForeRestrictives jrels
			o' <- quantify m $ andMPred $ (isAmong o):rps
			return (o',jrels')
		 return (o,jrels)
	(QSelbri q rels sb) -> do
	    m <- parseMex q
	    sr <- selbriToPred sb
	    (rps,jrels) <- stripForeRestrictives <$> parseRels rels
	    o <- quantify m (andMPred $ sr:rps)
	    return (o,jrels)
    o <- foldM doRel o jrels
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

data JboRelClause
    = JRRestrictive {jrrPred::JboPred}
    | JRIncidental {jriPred::JboPred}
    | JRAssign (Either SumtiAtom JboTerm)

parseRels :: PreProp r => [RelClause] -> ParseM r [JboRelClause]
parseRels rels = concat . map maybeToList <$> mapM parseRel rels where
    parseRel (Restrictive ss) = Just . JRRestrictive <$> subsentToPred ss RelVar
    parseRel (Descriptive ss) = Just . JRRestrictive <$> nonveridicialPred <$> subsentToPred ss RelVar
    parseRel (Incidental ss) = 
	(Just . JRIncidental <$>) $ subsentToPred ss RelVar >>= doQuestionsPred True
    parseRel (RestrictiveGOI goi t) = goiRel goi JRRestrictive t
    parseRel (IncidentalGOI goi t) = goiRel goi JRIncidental t
    parseRel (Assignment (Term [] (Just (Sumti Untagged (QAtom Nothing [] sa))))) | isAssignable sa = 
	return $ Just . JRAssign $ Left sa
    parseRel (Assignment t) = do
	ret <- ignoringArgs $ parseTerm t
	case ret of
	    Just (Right o) -> return $ Just . JRAssign $ Right o
	    _ -> return Nothing
    goiRel goi jr t = do
	ret <- ignoringArgs $ parseTerm t
	return $ jr <$> case ret of
	    Just (Right o) ->
		let rel = case goi of
			"pe" -> Brivla "srana"
			"ne" -> Brivla "srana"
			"po'u" -> Equal
			"no'u" -> Equal
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
stripForeRestrictives :: [JboRelClause] -> ([JboPred],[JboRelClause])
stripForeRestrictives rels = let (rrs,rels') = break (not . jrIsRes) rels in (map jrrPred rrs,rels')
    where
	jrIsRes (JRRestrictive _) = True
	jrIsRes _ = False
segregateRels :: [JboRelClause] -> ([JboPred],[JboPred],[Either SumtiAtom JboTerm])
segregateRels (r:rs) = let (rrs,irs,as) = segregateRels rs in case r of
	JRRestrictive p -> (p:rrs,irs,as)
	JRIncidental p ->  (rrs,p:irs,as)
	JRAssign a ->  (rrs,irs,a:as)
segregateRels [] = ([],[],[])

doRel :: PreProp r => JboTerm -> JboRelClause -> ParseM r JboTerm
doRel o (JRIncidental p) = doIncidental o p
doRel o (JRRestrictive p) = do
    -- XXX: ko'a poi broda -> zo'e noi me ko'a gi'e broda
    -- TODO: consider alternative semantics (Chierchia's iota?)
    o' <- getFreshConstant
    o' <- doIncidentals o' $ [p,isAmong o]
    return o'
doRel o (JRAssign a) = doAssign o a

parseVariable :: PreProp r => SumtiAtom -> [JboPred] -> Maybe JboMex -> ParseM r JboTerm
parseVariable sa@(Variable n) rps mm = do
    x <- lookupVarBinding sa
    case (x,mm) of
	 (Just o,Nothing) -> return o
	 _ -> do
	    o <- quantify (fromMaybe mexExists mm) $ andMPred rps
	    setVarBinding sa o
	    return o

parseSumtiAtom :: PreProp r => SumtiAtom -> ParseM r (JboTerm, [JboRelClause])
parseSumtiAtom sa = do
    jrels <- case sa of
	Description gadri _ _ _ rels _ -> if gadri!!1 == 'a' then return [] else parseRels rels
	QualifiedSumti _ rels _ -> parseRels rels
	Name _ rels _ ->
	    -- XXX: this construction, LA relativeClauses CMENE, appears not
	    -- to be mentioned in CLL; an alternative plausible semantics
	    -- would be that the relative clauses become "part of the name",
	    -- as with inner relative clauses in LA description sumti.
	    parseRels rels
	_ -> return []
    o <- case sa of
	Description gadri mis miq ssb rels irels -> do
	    extrairels <- if gadri!!1 == 'a' then parseRels rels else return []
	    mm <- traverse parseMex miq
	    sr <- case ssb of
		Left sb -> selbriToPred sb
		Right s -> isAmong <$> parseSumti s
	    (irps,iips,ias) <- (segregateRels . (extrairels++) <$>) $ parseRels $
		irels ++ maybeToList ((\is ->
		    IncidentalGOI "ne" (Term [] $ Just $ Sumti Untagged is)) <$> mis)
	    let xorlo_ps = sr : 
		    (case mm of
			Just m -> [(\o -> Rel (Moi (Value m) "mei") [o])]
			_ -> [])
	    o <- case gadri!!1 of
		'o' -> do
		    o <- getFreshConstant
		    doIncidentals o $ xorlo_ps ++ irps ++ iips
		'e' -> do
		    o <- getFreshConstant
		    doIncidental o $ nonveridicialPred $ andPred $ xorlo_ps ++ irps ++ iips
		'a' -> return $ PredNamed $ andPred $ xorlo_ps ++ irps ++ iips
		_ -> error "You call that a gadri?"
	    doAssigns o ias
	    return o
	QualifiedSumti qual _ s -> do
	    o <- parseSumti s
	    return $ QualifiedTerm qual o
	MexLi m -> Value <$> parseMex m
	MexMex m -> return $ TheMex m
	RelVar _ -> getVarBinding sa
	LambdaVar _ -> getVarBinding sa
	Ri _ -> getSumbasti sa
	Ra _ -> getSumbasti sa
	Assignable _ -> getSumbasti sa
	LerfuString _ -> getSumbasti sa
	MainBridiSumbasti _ -> getSumbasti sa
	SumtiQ kau -> addSumtiQuestion kau
	Zohe -> getFreshConstant
	-- TODO: following ought all to give fresh constants, really
	NonAnaphoricProsumti ps -> return $ NonAnaph ps
	Name _ _ s -> return $ Named s -- TODO: handle gadri
	Quote text ->
	    -- TODO: should probably return the unparsed text as well?
	    return $ JboQuote . ParsedQuote . evalParseStateM . evalText $ text
	ErrorQuote vs -> return $ JboErrorQuote vs
	NonJboQuote s -> return $ JboNonJboQuote s
	Word s -> return $ Valsi s
    let gadri = case sa of
	    Description gadri _ _ _ _ _ -> Just gadri
	    Name gadri _ _ -> Just gadri
	    _ -> Nothing
    o <- case drop 2 <$> gadri of
	Just s | s `elem` ["i","'i"] -> do -- lai/lei/loi/la'i/le'i/lo'i
	    o' <- getFreshConstant
	    let collector = Brivla $ if s == "i" then "gunma" else "selcmi"
	    doIncidental o' $ \x -> Rel collector [x,o]
	    return o'
	_ -> return o
    updateSumbastiWithSumtiAtom sa o
    return (o,jrels)

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
parseTagUnit (CAhA c) = return $ CAhA c
parseTagUnit (BAI c) = return $ BAI c
parseTagUnit (FAhA m c) = return $ FAhA m c
parseTagUnit (TAhE_ZAhO f c) = return $ TAhE_ZAhO f c
parseTagUnit (ROI r f q) = ROI r f <$> parseMex q
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

mexExists = (MexNumeralString [PA "su'o"])
mexForall = (MexNumeralString [PA "ro"])
terpJboMexAsQuantifier :: JboMex -> JboQuantifier
    -- TODO: implement xorxes' rules at
    -- http://www.lojban.org/tiki/BPFK+Section%3A+Inexact+Numbers ?
terpJboMexAsQuantifier m | m == mexForall = LojQuantifier Forall
terpJboMexAsQuantifier m | m == mexExists = LojQuantifier Exists
terpJboMexAsQuantifier (MexInt n) = LojQuantifier $ Exactly n
terpJboMexAsQuantifier m = MexQuantifier m

nullMex = MexNumeralString [PA "tu'o"]
nullOp = OpVUhU "ge'a"
parseMex,_parseMex :: PreProp r => Mex -> ParseM r JboMex
parseMex m = reduceMex <$> _parseMex m where
    reduceMex :: JboMex -> JboMex
    reduceMex (Operation op ms) = applyJboOperator op ms
    reduceMex m = m
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
_parseMex (ConnectedMex fore con@(JboConnLog _ _) m1 m2) = do
    doConnective fore con
	(_parseMex m1)
	(_parseMex m2)
_parseMex (ConnectedMex fore con@(JboConnJoik _ _) m1 m2) =
    ConnectedMex fore <$> parseConnective con <*> _parseMex m1 <*> _parseMex m2
_parseMex (Operation op ms) = Operation <$> parseOperator op <*> mapM _parseMex ms
_parseMex (MexArray ms) = MexArray <$> mapM _parseMex ms
_parseMex (QualifiedMex q m) = QualifiedMex q <$> _parseMex m
_parseMex (MexSelbri sb) = MexSelbri <$> selbriToPred sb
_parseMex (MexSumti s) = MexSumti <$> parseSumti s
_parseMex (MexInt n) = return $ MexInt n
_parseMex (MexNumeralString ns) = return $ MexNumeralString ns
_parseMex (MexLerfuString ls) = return $ MexLerfuString ls
parseOperator :: PreProp r => Operator -> ParseM r JboOperator
parseOperator (ConnectedOperator fore con@(JboConnLog _ _) o1 o2) = do
    doConnective fore con
	(parseOperator o1)
	(parseOperator o2)
parseOperator (ConnectedOperator fore con@(JboConnJoik _ _) o1 o2) =
    ConnectedOperator fore <$> parseConnective con <*> parseOperator o1 <*> parseOperator o2
parseOperator (OpPermuted s o) = OpPermuted s <$> parseOperator o
parseOperator (OpScalarNegated n op) = OpScalarNegated n <$> parseOperator op
parseOperator (OpMex m) = OpMex <$> _parseMex m
parseOperator (OpSelbri sb) = OpSelbri <$> selbriToPred sb
parseOperator (OpVUhU v) = return $ OpVUhU v

quantify :: PreProp r => JboMex -> Maybe JboPred -> ParseM r JboTerm
quantify m r = do
    fresh <- getFreshVar $ maybe UnrestrictedDomain PredDomain r
    mapProp $ \p ->
	Quantified (terpJboMexAsQuantifier m) (jboPredToLojPred <$> r) $
	    \v -> subTerm fresh (BoundVar v) p
    return fresh

doTag :: PreProp r => JboTag -> Maybe JboTerm -> ParseM r ()
doTag (DecoratedTagUnits dtus) Nothing =
    -- separate into a stream of possibly negated modals
    -- (no obvious way to make sense of this with JOI connection,
    -- and doesn't fit current sumtcita handling)
    mapM_ doDTU dtus where
	doDTU dtu = do
	    let scalar = tagNaiIsScalar $ tagUnit dtu
	    when (tagNAI dtu && not scalar) $ mapProp Not
	    doModal $ JboTagged (DecoratedTagUnits [dtu{tagNAI=(tagNAI dtu && scalar)}]) Nothing
doTag jtag mt = doModal $ JboTagged jtag mt

doBareTag :: PreProp r => JboTag -> ParseM r ()
doBareTag tag = doTag tag Nothing

doModal :: PreProp r => JboModalOp -> ParseM r ()
doModal op = mapProp (Modal op)

nonveridicialPred :: JboPred -> JboPred
nonveridicialPred p t = Modal NonVeridicial $ p t

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
    fresh <- getFreshVar UnrestrictedDomain
    p <- runSubBridiM $ m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> ParseM r JboPred
subsentToPred ss rv = do
    fresh@(Var n) <- getFreshVar UnrestrictedDomain
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
	    v <- quantify mexExists Nothing
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
