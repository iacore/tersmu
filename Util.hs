module Util where

swap :: [a] -> Int -> Int -> [a]
swap as n m = [ if i == n then as!!m else
		if i == m then as!!n else as!!i | i <- [0..] ]

swapFinite as n m = take (length as) $ swap as n m

swapFiniteWithDefault :: a -> [a] -> Int -> Int -> [a]
swapFiniteWithDefault def ts n m = take (max (max n m + 1) (length ts)) $
	swap (ts ++ repeat def) n m
