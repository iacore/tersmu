module JboShow where

import Bindful
import JboSyntax
import JboProp
import FOL hiding (Term)
import Util

import Data.Maybe
import Control.Applicative
import Data.Traversable (traverse)
import Data.List

---- Printing routines, in lojban and in (customized) logical notation

instance Rel JboRel where
    relstr r = evalBindful $ logshow r

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

bracket :: Char -> String -> String
bracket c =
    let c' = case c of
	    '(' -> ')'
	    '[' -> ']'
	    '{' -> '}'
	    '<' -> '>'
	    '"' -> '"'
	    '\'' -> '\''
    in (c:) . (++[c'])

jbobracket :: String -> String -> String -> String
jbobracket l r = ((l++" ")++) . (++(" "++r))

instance JboShow String where
    logjboshow _ s = return s

instance JboShow JboQuantifier where
    logjboshow _ QuestionQuantifier = return "ma"
    logjboshow jbo (LojQuantifier q) = logjboshow jbo q
    logjboshow jbo (MexQuantifier m) = logjboshow jbo m
instance JboShow LojQuantifier where
    jboshow Exists = return "su'o"
    jboshow Forall = return "ro"
    jboshow (Exactly n) = return $ jbonum n
    logshow = return . show

logjboshowlist :: JboShow a => Bool -> [a] -> Bindful SumtiAtom String
logjboshowlist jbo as = do
    ass <- mapM (logjboshow jbo) as
    return $ concat $ intersperse (if jbo then " " else ",") ass 

instance JboShow Mex where
    logjboshow _ m = return $ show m
instance JboShow JboMex where
    logjboshow jbo (Operation op ms) = do
	ops <- logjboshow jbo op
	mss <- logjboshowlist jbo ms
	return $ if jbo
	    then "pe'o "++ops++" "++mss++" ku'e"
	    else ops++"("++mss++")"
    logjboshow jbo (ConnectedMex fore con m m') = do
	[ms,ms'] <- mapM (logjboshow jbo) [m,m']
	cs <- logjboshowConn jbo "." con
	if jbo
	    then return $ "vei " ++ ms ++" ve'o " ++ cs ++ " vei " ++ ms' ++ " ve'o"
	    else return $ "(" ++ ms ++ ")" ++ cs ++ "(" ++ ms' ++ ")"
    logjboshow jbo (QualifiedMex qual t) = do
	ts <- logjboshow jbo t
	let quals = case qual of {LAhE l -> l; NAhE_BO n -> n ++ " bo"}
	return $ if jbo
	    then quals ++ " " ++ ts ++ " lu'u"
	    else "{" ++ quals ++ "}(" ++ ts ++ ")"
    logjboshow jbo@True (MexInt n) = (++" boi") <$> logjboshow jbo n
    logjboshow jbo@False (MexInt n) = logjboshow jbo n
    logjboshow jbo@True (MexNumeralString ns) = (++" boi") <$> logjboshowlist jbo ns
    logjboshow jbo@False (MexNumeralString ns) = bracket '(' <$> logjboshowlist True ns
    logjboshow jbo@True (MexLerfuString ls) = (++" boi") <$> logjboshow jbo ls
    logjboshow jbo@False (MexLerfuString ls) = bracket '(' <$> logjboshow True ls
    logjboshow jbo@False (MexSelbri p) = bracket '[' <$> logjboshow jbo p
    logjboshow jbo@True (MexSelbri p) = jbobracket "ni'e" "te'u" <$> logjboshow jbo p
    logjboshow jbo@False (MexSumti t) = bracket '[' <$> logjboshow jbo t
    logjboshow jbo@True (MexSumti t) = jbobracket "mo'e" "te'u" <$> logjboshow jbo t
    logjboshow jbo@False (MexArray ms) = bracket '[' <$> logjboshowlist jbo ms
    logjboshow jbo@True (MexArray ms) = jbobracket "jo'i" "te'u" <$> logjboshowlist jbo ms

-- |logjboshownumber: for cases when we shouldn't append a {boi} (number and
-- numberOrLerfuString productions)
logjboshownumber :: Bool -> JboMex -> Bindful SumtiAtom String
logjboshownumber _ m | not (mexIsNumberOrLS m) = error "[BUG: Full mex in ljsn]"
logjboshownumber jbo (MexInt n) = logjboshow jbo n
logjboshownumber jbo@True (MexNumeralString ns) = logjboshowlist jbo ns
logjboshownumber jbo@False (MexNumeralString ns) = bracket '(' <$> logjboshowlist True ns
logjboshownumber jbo@True (MexLerfuString ls) = logjboshow jbo ls
logjboshownumber jbo@False (MexLerfuString ls) = bracket '(' <$> logjboshow True ls

instance JboShow Numeral where
    logjboshow True (PA pa) = return pa
    logjboshow False (PA pa) = return $ "{" ++ pa ++ "}"
    logjboshow jbo (NumeralLerfu l) = logjboshow jbo l

instance JboShow [Lerfu] where
    logjboshow jbo ls =
	concat . (if jbo then intersperse " " else id) <$> mapM (logjboshow jbo) ls
instance JboShow Lerfu where
    logjboshow True (Lerfu c) = return $ case c of
	_ | c `elem` "aoeui" -> (c:"bu")
	'y' -> "y bu"
	'h' -> "y'y"
	_ | c `elem` ['0'..'9'] -> jbonum $ fromEnum c - fromEnum '0'
	_ -> c:"y"
    logjboshow False (Lerfu c) = return $ [c]

instance JboShow JboOperator where
    logjboshow jbo (ConnectedOperator _ con op op') = do
	[ops,ops'] <- mapM (logjboshow jbo) [op,op']
	cs <- logjboshowConn jbo "j" con
	if jbo
	    then return $ "ke " ++ ops ++ " ke'e " ++ cs ++ " ke " ++ ops' ++ " ke'e"
	    else return $ "<" ++ ops ++ ">" ++ cs ++ "<" ++ ops' ++ ">"
    logjboshow jbo (OpPermuted s o) =
	((seToStr s ++ " ") ++) <$> logjboshow jbo o
    logjboshow jbo (OpScalarNegated n op) = do
	ops <- logjboshow jbo op
	return $ if jbo then n ++ " " ++ ops else "{"++n++"}("++ops++")"
    logjboshow jbo@False (OpMex m) = bracket '[' <$> logjboshow jbo m
    logjboshow jbo@True (OpMex m) = jbobracket "ma'o" "te'u" <$> logjboshow jbo m
    logjboshow jbo@False (OpSelbri s) = bracket '[' <$> logjboshow jbo s
    logjboshow jbo@True (OpSelbri s) = jbobracket "na'u" "te'u" <$> logjboshow jbo s
    logjboshow jbo@False (OpVUhU v) = bracket '{' <$> return v
    logjboshow jbo@True (OpVUhU v) = return v

logjboshowLogConn _ prefix (LogJboConnective b c b') =
	return $ (if not b then "na " else "") ++
	    prefix ++ [c] ++
	    if not b' then " nai" else ""

logjboshowConn False prefix con = do
    js <- logjboshowConn True prefix con
    return $ "{"++js++"}"
logjboshowConn True prefix (JboConnLog mtag lcon) = do
    lc <- logjboshowLogConn True prefix lcon
    mtags <- maybe "" ((" "++).(++" bo")) <$> traverse (logjboshow True) mtag
    return $ lc ++ mtags
logjboshowConn True prefix (JboConnJoik mtag joik) = do
    jois <- logjboshow True joik
    mtags <- maybe "" ((" "++).(++" bo")) <$> traverse (logjboshow True) mtag
    return $ jois ++ mtags

instance JboShow JboTag where
    logjboshow jbo (ConnectedTag con tag1 tag2) = do
	[s1,s2] <- mapM (logjboshow jbo) [tag1,tag2]
	conns <- logjboshowConn jbo "." con
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else conns ++ "(" ++ s1 ++ "," ++ s2 ++ ")"
    logjboshow jbo (DecoratedTagUnits dtus) =
	(concat.intersperse " " <$>) $ (`mapM` dtus)
	$ \(DecoratedTagUnit nahe se nai tu) -> do
	    tus <- logjboshow jbo tu
	    return $ maybe "" (++" ") nahe
		++ maybe "" ((++" ").seToStr) se
		++ tus
		++ if nai then " nai" else ""
instance JboShow JboTagUnit where
    logjboshow jbo (TenseCmavo s) = return s
    logjboshow jbo (BAI s) = return s
    logjboshow jbo (FAhA mohi s) = return $
	(if mohi then "mo'i " else "") ++ s
    logjboshow jbo (ROI r fehe q) = do
	qs <- logjboshownumber jbo q
	return $ 
	    (if fehe then "fe'e " else "") ++ qs ++ " " ++ r
    logjboshow jbo (TAhE_ZAhO fehe s) = return $
	(if fehe then "fe'e " else "") ++ s
    logjboshow jbo (FIhO p) = do
	ps <- logjboshow jbo p
	return $ "fi'o " ++ ps ++ if jbo then " fe'u" else ""
    logjboshow jbo KI = return "ki"
    logjboshow jbo CUhE = return "cu'e(TODO!)"

instance JboShow Abstractor where
    logjboshow _ (NU n) = return n
    logjboshow jbo (NegatedAbstractor a) = (++"nai") <$> logjboshow jbo a
    logjboshow jbo (LogConnectedAbstractor con a1 a2) = do
	[s1,s2] <- mapM (logjboshow jbo) [a1,a2]
	conns <- logjboshowLogConn jbo "j" con
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else "({" ++ conns ++ "}(" ++ s1 ++ "," ++ s2 ++ "))"
    logjboshow jbo (JoiConnectedAbstractor joik a1 a2) = do
	[s1,s2] <- mapM (logjboshow jbo) [a1,a2]
	conns <- logjboshow jbo joik
	return $ if jbo
	    then s1 ++ " " ++ conns ++ " " ++ s2
	    else "({" ++ conns ++ "}(" ++ s1 ++ "," ++ s2 ++ "))"

instance JboShow JboPred where
    logjboshow jbo p = logjboshowpred jbo (\n -> p (BoundVar n))

logjboshowpred jbo@False p =
    withShuntedRelVar $ \n -> logjboshow jbo $ p n
logjboshowpred jbo@True p = withNextVariable $ \v ->
     case p v of
	 Rel sb ts | isJust $ elemIndex (BoundVar v) ts -> do
	     s <- logjboshow jbo sb
	     let i = 1 + fromJust (elemIndex (BoundVar v) ts)
		 ts' = tail $ case i of
			 1 -> ts
			 _ -> swapFinite ts 0 (i-1)
		 s' = case i of
			 1 -> s
			 _ -> seToStr i ++ " " ++ s
	     case ts' of
		 [] -> return s'
		 _ -> do
		     tss <- sequence $ map (logjboshow jbo) ts'
		     return $ s' ++ " be " ++ concat (intersperse " bei " tss)
	 _ -> withShuntedRelVar $ \n -> do
		 s <- logjboshow jbo (p n)
		 return $ "poi'i " ++ s ++ " kei"

instance JboShow JboRel where
    {-
    logjboshow jbo (ConnectedRels conn r r') = do
	s <- logjboshow jbo r
	s' <- logjboshow jbo conn
	s'' <- logjboshow jbo r'
	return $ if jbo
	    then s ++ " " ++ s' ++ " " ++ s''
	    else "(" ++ s ++ " " ++ s' ++ " " ++ s'' ++ ")"
    logjboshow jbo (PermutedRel n r) =
	((seToStr n ++ " ") ++) <$> logjboshow jbo r
    -}
    logjboshow jbo (TanruConnective con p p') = do
	[ps,ps'] <- mapM (logjboshow jbo) [p,p']
	cs <- logjboshowConn jbo "j" con
	if jbo
	    then return $ "ke " ++ ps ++ " ke'e " ++ cs ++ " ke " ++ ps' ++ " ke'e"
	    else return $ "<" ++ ps ++ ">" ++ cs ++ "<" ++ ps' ++ ">"
    logjboshow jbo (Tanru p r) =
      do rstr <- logjboshow jbo r
	 pstr <- logjboshow jbo p
	 if jbo
	    then return $ "ke " ++ pstr ++ " " ++ rstr ++ " ke'e"
	    else return $ "<" ++ pstr ++ "><" ++ rstr ++ ">"
    logjboshow jbo (ScalarNegatedRel n r) = do
	rs <- logjboshow jbo r
	return $ if jbo then n ++ " " ++ rs else "{"++n++"}("++rs++")"
    logjboshow jbo (Moi (Value q) m) | mexIsNumberOrLS q = do
	s <- logjboshownumber jbo q
	return $ s ++ " " ++ m
    logjboshow jbo (Moi t m) = do
	ts <- logjboshow jbo t
	return $ if jbo then "me " ++ ts ++ " me'u " ++ m
	    else bracket '[' ts ++ " " ++ m
    logjboshow jbo (AbsPred a p) =
	do withShuntedLambda (\n -> do
	    ps <- logjboshow jbo (p (BoundVar n))
	    as <- logjboshow jbo a
	    return $ if jbo then as ++ " " ++ ps ++ " kei" 
		else as ++ "[" ++ ps ++ "]" )
    logjboshow jbo (AbsProp a p) = do
	ps <- logjboshow jbo p
	as <- logjboshow jbo a
	return $ if jbo then as ++ " " ++ ps ++ " kei" 
		else as ++ "[" ++ ps ++ "]"
    logjboshow jbo (Among t) = do
	s <- logjboshow jbo t
	return $ if jbo then "me " ++ s ++ " me'u" else "Among[" ++ s ++ "]"
    logjboshow jbo Equal =
	return $ if jbo then "du" else "="
    logjboshow jbo (UnboundBribasti (TUGOhA g n)) = return $
	(if jbo then unwords else concat) $
	    g : if n==1 then [] else ["xi",jbonum n]
    logjboshow jbo (UnboundBribasti (TUBrivla s)) = return s
    logjboshow jbo (OperatorRel op) =
	(if jbo then jbobracket "nu'a" "te'u" else bracket '[') <$> logjboshow jbo op
    logjboshow jbo (TagRel tag) = do
	tags <- logjboshow jbo tag
	return $ if jbo then "xo'i " ++ tags else "{" ++ tags ++ "}"
    logjboshow _ (Brivla s) = return s

instance JboShow SumtiAtom where
    logjboshow jbo (LerfuString s) = logjboshow jbo s
    logjboshow jbo v =
	if jbo then return $ case v of
	    Variable n | n <= 3 -> "d" ++ vowelnum n
	    Variable n -> "da xi " ++ jbonum n
	    RelVar 1 -> "ke'a"
	    RelVar n -> "ke'a xi " ++ jbonum n
	    LambdaVar 1 -> "ce'u"
	    LambdaVar n -> "ce'u xi " ++ jbonum n
	    Assignable n | n <= 5 -> "ko'" ++ vowelnum n
	    Assignable n | n <= 10 -> "fo'" ++ vowelnum (n-5)
	    Assignable n -> "ko'a xi " ++ jbonum n
	    Ri 1 -> "ri"
	    Ri n -> "ri xi " ++ jbonum n
	    Ra r -> r
	    MainBridiSumbasti n | n <= 5 -> "vo'" ++ vowelnum n
	    MainBridiSumbasti n -> "vo'a xi " ++ jbonum n
	else case v of
	    Variable n -> return $ "x" ++ show n
	    RelVar 1 -> return $ "_"
	    RelVar n -> return $ "_" ++ show n
	    LambdaVar n -> return $ "\\" ++ show n
	    v -> do
		s <- logjboshow True v
		return $ "{" ++ s ++ "}"
instance JboShow JboTerm where
    logjboshow False (ZoheTerm) = return " "
    logjboshow True (ZoheTerm) = return "zo'e"
    logjboshow jbo (BoundVar n) = binding n >>= logjboshow jbo
    logjboshow jbo (Var n) = return $ if jbo then "lo XASLI zei da ku" else "[DONKEY]"
    logjboshow True (Constant n []) = return $ "cy " ++ jbonum n
    logjboshow False (Constant n []) = return $ "c" ++ show n
    logjboshow jbo (Constant n ts) = do
	ss <- mapM (logjboshow jbo) ts
	return $ if jbo
	    then "li ma'o fy" ++ jbonum n ++ " " ++
		(concat . intersperse " " $ (map ("mo'e "++) ss)) ++ " lo'o"
	    else "f" ++ show n ++ "(" ++
		(concat . intersperse "," $ ss) ++ ")"
    logjboshow True (Named s) = return $ "la " ++ s ++ "."
    logjboshow False (Named s) = return $ bracket '"' s
    logjboshow jbo (JboQuote (ParsedQuote ps)) = do
	pss <- logjboshow jbo ps
	return $
	    (if jbo then "lu " else "<< ") ++
	    pss ++
	    (if jbo then " li'u" else " >>")
    logjboshow jbo (JboErrorQuote vs) = return $
	(if jbo then "lo'u " else "<{< ") ++
	unwords vs ++
	(if jbo then " le'u" else " >}>")
    logjboshow jbo (JboNonJboQuote s) = return $
	let zoik = head
		[ zoik
		| n <- [0..]
		, let zoik = "zoi" ++ if n > 0 then ("k"++) $ concat $ replicate (n-1) "yk" else ""
		, not $ isInfixOf zoik s ]
	in (if jbo then "zoi " ++ zoik ++ " " else "<[< ") ++
	    s ++
	    (if jbo then " " ++ zoik else " >]>")
    logjboshow True (Valsi s) = return $ "zo " ++ s
    logjboshow False (Valsi s) = return $ "{" ++ s ++ "}"
    logjboshow jbo (UnboundSumbasti sa) = logjboshow jbo sa
    logjboshow _ (NonAnaph s) = return s
    logjboshow jbo (JoikedTerms joik t1 t2) = do
	[ts1,ts2] <- mapM (logjboshow jbo) [t1,t2]
	joiks <- logjboshow jbo joik
	return $ if jbo then ts1 ++ " " ++ joiks ++ " ke " ++ ts2 ++ " ke'e"
	    else "(" ++ ts1 ++ " {" ++ joiks ++ "} " ++ ts2 ++ ")"
    logjboshow jbo (QualifiedTerm qual t) = do
	ts <- logjboshow jbo t
	let quals = case qual of {LAhE l -> l; NAhE_BO n -> n ++ " bo"}
	return $ if jbo
	    then quals ++ " " ++ ts ++ " lu'u"
	    else "{" ++ quals ++ "}(" ++ ts ++ ")"
    logjboshow True (Value m) = ("li "++) . (++" lo'o") <$> logjboshow True m
    logjboshow False (Value m) = logjboshow False m
    logjboshow True (TheMex m) = ("me'o "++) . (++" lo'o") <$> logjboshow True m
    logjboshow False (TheMex m) = bracket '[' . ("MEX: "++) <$> logjboshow False m
	

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

instance JboShow Int where
    logjboshow True n = return $ jbonum n
    logjboshow False n = return $ show n

instance JboShow JboProp
    where {logjboshow jbo p = (if jbo then unwords else concat)
				<$> logjboshow' jbo [] p
	where
	  logjboshow' :: Bool -> [String] -> JboProp -> Bindful SumtiAtom [String]
	  {-
	  logjboshow' True ps (Quantified (Gadri gadri) r p) =
	      withNextAssignable $ \n ->
		  do vs <- logjboshow jbo (BoundVar n)
		     rss <- logjboshowpred jbo (fromJust r)
		     logjboshow' jbo (ps ++ [gadri] ++ [rss] ++
			 ["ku","goi",vs]) (p n)
	  -}
	  logjboshow' True ps (Quantified QuestionQuantifier _ p) =
	      withNextAssignable $ \n ->
		  do as <- logjboshow jbo (BoundVar n)
		     logjboshow' jbo (ps ++ ["ma","goi",as]) (p n)
	  logjboshow' jbo ps (Quantified q r p) =
	      withNextVariable $ \n ->
		  do qs <- logjboshow jbo q
		     vs <- logjboshow jbo (BoundVar n)
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
	  logjboshow' jbo ps (Modal (WithEventAs t) p) = do
	    ts <- logjboshow jbo t
	    logjboshow' jbo (ps ++ if jbo then ["fi'o","du"] ++ [ts] else [ts] ++ ["=. "]) p
	  logjboshow' jbo ps (Modal QTruthModal p) =
	    logjboshow' jbo (ps ++ if jbo then ["xu","kau"] else ["?. "]) p
	  logjboshow' jbo ps (Modal (JboTagged tag mt) p) = do
	    tags <- logjboshow jbo tag
	    mtl <- maybeToList <$> traverse (logjboshow jbo) mt
	    logjboshow' jbo (ps ++ if jbo
		then [tags] ++ mtl ++ ["ku"]
		else ["(",tags,")","("] ++ mtl ++ ["). "]) p
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
	  logjboshow' jbo ps (NonLogConnected joik p1 p2) =
	      do ss1 <- logjboshow' jbo ps p1
	         ss2 <- logjboshow' jbo ps p2
		 joiks <- logjboshow jbo joik
	         return $ if jbo then [joik,"gi"]
	      			++ ss1 ++ ["gi"] ++ ss2
	      		   else ["("] ++ ss1 ++
	      		        [" {"++joik++"} "] ++ ss2 ++ [")"]
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

instance JboShow [JboProp] where
    jboshow ps = concat . intersperse "\n.i " <$> mapM jboshow ps
    logshow ps = concat . intersperse "\n" <$> mapM logshow ps
