module Bindful where

-- monad to conveniently handle binding values to numbered variables

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

class (Monad m) => BindfulMonad s m | m -> s where
    withBinding :: s -> (Int -> m r) -> m r
    binding :: Int -> m s
    twiddleBound :: (s -> s) -> m ()
    getValues :: m [s]
    evalBindful :: m a -> a

    -- intended to be private:
    nextFree :: m Int
    bind :: Int -> s -> m ()
    unbind :: Int -> m ()
    bindNext :: s -> m ()

type Bindful s = State (Map Int s)

instance BindfulMonad s (Bindful s) where
    withBinding v f = do n <- nextFree
			 bind n v
			 r <- f n
			 unbind n
			 return r
    binding n = do bs <- get
		   case Map.lookup n bs of
			  Nothing -> error $ show n ++ " unbound"
			  Just v -> return v
    getValues = gets Map.elems
    twiddleBound f = do ks <- gets Map.keys
			sequence_ $ [ do s <- binding n
					 bind n (f s)
				      | n <- ks ]
    evalBindful m = evalState m Map.empty

    nextFree = do bs <- get
		  return $ head [ n |
		      n <- [1..], isNothing $ Map.lookup n bs ]
    bind n v = do bs <- get
		  put $ Map.insert n v bs
    unbind n = do bs <- get
		  put $ Map.delete n bs
    bindNext v = do n <- nextFree
		    bind n v
