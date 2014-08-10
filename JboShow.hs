module JboShow where

import Bindful
import JboSyntax
import JboProp
import FOL hiding (Term)
import Util

import Data.Maybe
import Control.Applicative
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

instance JboShow Quantifier where
    jboshow Exists = return "su'o"
    jboshow Forall = return "ro"
    jboshow (Exactly n) = return $ show n
    logshow = return . show
instance JboShow JboConnective where
    logjboshow _ (JboConnective b c b') =
	return $ (if not b then "na." else "") ++
	    [c] ++
	    if not b' then "nai" else ""

logjboshowpred jbo p = withShuntedRelVar (\n ->
   if not jbo
     then logjboshow jbo (p n)
     else case p n of
	   Rel sb ts | isJust $ elemIndex (Var n) ts ->
	       do s <- logjboshow jbo sb
		  let i = 1 + fromJust (elemIndex (Var n) ts)
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
    logjboshow jbo (ConnectedRels conn r r') = do
	s <- logjboshow jbo r
	s' <- logjboshow jbo conn
	s'' <- logjboshow jbo r'
	return $ if jbo
	    then s ++ " " ++ s' ++ " " ++ s''
	    else "(" ++ s ++ " " ++ s' ++ " " ++ s'' ++ ")"
    logjboshow jbo (PermutedRel n r) =
	((seToStr n ++ " ") ++) <$> logjboshow jbo r
    logjboshow jbo (Tanru p r) =
      do rstr <- logjboshow jbo r
	 pstr <- logjboshowpred jbo (\n -> p (Var n))
	 if jbo
	    then return $ "ke " ++ pstr ++ " " ++ rstr ++ " ke'e"
	    else return $ "<" ++ pstr ++ "><" ++ rstr ++ ">"

    logjboshow jbo (Moi q m) = do s <- logjboshow jbo q
				  return $ s ++ " " ++ m
    logjboshow jbo (AbsPred a p) =
	do withShuntedLambda (\n ->
	       do s <- logjboshow jbo (p (Var n))
		  return $ if jbo then a ++ " " ++ s ++ " kei" 
				  else a ++ "[" ++ s ++ "]" )
    logjboshow jbo (AbsProp a p) =
	do s <- logjboshow jbo p
	   return $ if jbo then a ++ " " ++ s ++ " kei"
			   else a ++ "[" ++ s ++ "]"
    logjboshow jbo (Among t) = do
	s <- logjboshow jbo t
	return $ if jbo then "me " ++ s ++ " me'u" else "Among[" ++ s ++ "]"
    logjboshow _ (Brivla s) = return s

instance JboShow JboTerm where
    logjboshow False (ZoheTerm) = return " "
    logjboshow True (ZoheTerm) = return "zo'e"
    logjboshow jbo (Var n) =
	do v <- binding n 
	   return $ if jbo then case v of
				    Variable n | n <= 3 -> "d" ++ vowelnum n
				    Variable n -> "da xi " ++ jbonum n
				    RelVar 1 -> "ke'a"
				    RelVar n -> "ke'a xi " ++ jbonum n
				    LambdaVar 1 -> "ce'u"
				    LambdaVar n -> "ce'u xi " ++ jbonum n
				    Assignable n | n <= 5 -> "ko'" ++ vowelnum n
				    Assignable n | n <= 10 -> "fo'" ++ vowelnum (n-5)
				    Assignable n -> "ko'a xi " ++ jbonum n
			    else case v of
				    Variable n -> "x" ++ show n
				    RelVar 1 -> "_"
				    RelVar n -> "_" ++ show n
				    LambdaVar n -> "\\" ++ show n
    logjboshow True (Named s) = return $ "la " ++ s ++ "."
    logjboshow False (Named s) = return s
    logjboshow True (JboQuote ss) = return $ "lu li'o li'u"
    logjboshow False (JboQuote ss) = return $ "\"...\""
    logjboshow True (Valsi s) = return $ "zo " ++ s
    logjboshow False (Valsi s) = return $ "{" ++ s ++ "}"
    logjboshow _ (UnboundAssignable n) = return $
	case n of _ | n <= 5 -> "ko'" ++ vowelnum n
	          _ | n <= 10 -> "fo'" ++ vowelnum (n-5)
		  _ -> "ko'a xi " ++ jbonum n
    logjboshow _ (UnboundLerfuString s) = return $ concat $ intersperse " " $
	map (\c -> case c of _ | c `elem` "aoeui" -> (c:"bu")
			     'y' -> "y bu"
			     _ -> (c:"y")) s
    logjboshow _ (NonAnaph s) = return s
	

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
	  logjboshow' True ps (Quantified (Gadri gadri) r p) =
	      withNextAssignable $ \n ->
		  do vs <- logjboshow jbo (Var n)
		     rss <- logjboshowpred jbo (fromJust r)
		     logjboshow' jbo (ps ++ [gadri] ++ [rss] ++
			 ["ku","goi",vs]) (p n)
	  logjboshow' jbo ps (Quantified q r p) =
	      withNextVariable $ \n ->
		  do qs <- logjboshow jbo q
		     vs <- logjboshow jbo (Var n)
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
