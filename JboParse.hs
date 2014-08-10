module JboParse where

import FOL hiding (Term)
import JboProp
import JboSyntax
import BridiM

import Data.Maybe
import Control.Monad
import Control.Applicative
import Data.List

parseStatements :: [Statement] -> BridiM JboProp
parseStatements ss = mapM parseStatement ss >>= return . bigAnd

parseStatement :: Statement -> BridiM JboProp
parseStatement (Statement ps s) = do
    ignoringArgs $ parseTerms ps
    parseStatement1 s

parseStatement1 :: Statement1 -> BridiM JboProp
parseStatement1 (ConnectedStatement con s1 s2) =
    do p1 <- parseStatement1 s1
       p2 <- parseStatement1 s2
       return $ connToFOL con p1 p2
parseStatement1 (StatementStatements ss) =
    parseStatements ss
parseStatement1 (StatementSentence s) = do
    -- TODO: assign go'i
    as <- getArglist
    runSubBridiM $ putArglist as >> parseSentence s

parseSubsentence :: Subsentence -> BridiM Bridi
parseSubsentence (Subsentence ps s) = do
    ignoringArgs $ parseTerms ps
    parseSentence s


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
	    (runSubBridiM $ parseSubsentence ss)
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
isAssignable (Name _) = True
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
    p <- runSubBridiM $ m <* addImplicit fresh
    return $ \o -> subTerm fresh o p 

subsentToPred :: Subsentence -> (Int -> SumtiAtom) -> BridiM JboPred
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


andPred :: [JboPred] -> JboPred
andPred ps x = bigAnd [p x | p <- ps]

andMPred :: [JboPred] -> Maybe JboPred
andMPred [] = Nothing
andMPred ps = Just $ andPred ps

isAmong :: JboTerm -> (JboTerm -> JboProp)
isAmong y = \o -> Rel (Among y) [o]
