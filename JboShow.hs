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

instance JboShow String where
    logjboshow _ s = return s

instance JboShow Quantifier where
    jboshow Exists = return "su'o"
    jboshow Forall = return "ro"
    jboshow (Exactly n) = return $ show n
    logshow = return . show

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
    logjboshow jbo (ROI fehe q) = do
	qs <- logjboshow jbo q
	return $ 
	    (if fehe then "fe'e " else "") ++ qs ++ " roi"
    logjboshow jbo (TAhE_ZAhO fehe s) = return $
	(if fehe then "fe'e " else "") ++ s
    logjboshow jbo (FIhO p) = do
	ps <- logjboshow jbo p
	return $ "fi'o " ++ ps ++ if jbo then " fe'u" else ""

instance JboShow JboPred where
    logjboshow jbo p = logjboshowpred jbo (\n -> p (BoundVar n))

-- FIXME: bugs with interactions between actual ke'a and these fake ones
-- e.g. du da poi du be fa ke'a du
logjboshowpred jbo p = withShuntedRelVar (\n ->
   if not jbo
     then logjboshow jbo (p n)
     else case p n of
	   Rel sb ts | isJust $ elemIndex (BoundVar n) ts ->
	       do s <- logjboshow jbo sb
		  let i = 1 + fromJust (elemIndex (BoundVar n) ts)
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

    logjboshow jbo (Moi q m) = do s <- logjboshow jbo q
				  return $ s ++ " " ++ m
    logjboshow jbo (AbsPred a p) =
	do withShuntedLambda (\n ->
	       do s <- logjboshow jbo (p (BoundVar n))
		  return $ if jbo then a ++ " " ++ s ++ " kei" 
				  else a ++ "[" ++ s ++ "]" )
    logjboshow jbo (AbsProp a p) =
	do s <- logjboshow jbo p
	   return $ if jbo then a ++ " " ++ s ++ " kei"
			   else a ++ "[" ++ s ++ "]"
    logjboshow jbo (Among t) = do
	s <- logjboshow jbo t
	return $ if jbo then "me " ++ s ++ " me'u" else "Among[" ++ s ++ "]"
    logjboshow jbo Equal =
	return $ if jbo then "du" else "="
    logjboshow jbo (UnboundBribasti (TUGOhA g n)) = return $
	(if jbo then unwords else concat) $
	    g : if n==1 then [] else ["xi",jbonum n]
    logjboshow jbo (UnboundBribasti (TUBrivla s)) = return s
    logjboshow _ (Brivla s) = return s

instance JboShow SumtiAtom where
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
	    Ri n -> "ri" ++ jbonum n
	    LerfuString s -> concat $ intersperse " " $
		map (\c -> case c of
		    _ | c `elem` "aoeui" -> (c:"bu")
		    'y' -> "y bu"
		    'h' -> "y'y"
		    _ | c `elem` ['0'..'9'] -> jbonum $ fromEnum c - fromEnum '0'
		    _ -> (c:"y")) s
	    MainBridiSumbasti n | n <= 5 -> "vo'" ++ vowelnum n
	    MainBridiSumbasti n -> "vo'a xi " ++ jbonum n
	else case v of
	    Variable n -> return $ "x" ++ show n
	    RelVar 1 -> return $ "_"
	    RelVar n -> return $ "_" ++ show n
	    LambdaVar n -> return $ "\\" ++ show n
	    LerfuString s -> return s
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
    logjboshow False (Named s) = return s
    logjboshow jbo (JboQuote (ParsedQuote ps)) = do
	pss <- logjboshow jbo ps
	return $
	    (if jbo then "lu " else "<< ") ++
	    pss ++
	    (if jbo then " li'u" else " >>")
    logjboshow jbo (JboErrorQuote vs) = return $
	(if jbo then "lo'u " else "{ ") ++
	unwords vs ++
	(if jbo then " le'u" else " }")
    logjboshow jbo (JboNonJboQuote s) = return $
	let zoik = head
		[ zoik
		| n <- [0..]
		, let zoik = "zoi" ++ if n > 0 then ("k"++) $ concat $ replicate (n-1) "yk" else ""
		, not $ isInfixOf zoik s ]
	in (if jbo then "zoi " ++ zoik ++ " " else "<< ") ++
	    s ++
	    (if jbo then " " ++ zoik else " >>")
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
