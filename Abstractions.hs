-- abstractions I've made along the way
-- not up-to-date
module Abstractions where

import Prelude hiding (lookup, foldr, foldl, length)
import Data.Traversable
import Data.Monoid
import Control.Applicative (Applicative, pure, (<*>), liftA2)
import Control.Monad
import Data.Foldable (find, Foldable, foldMap, foldr, foldl)
import qualified Data.List as List (nub, permutations)
import Data.Maybe (fromJust, isJust)
import Data.Array
import Data.Set hiding (map, foldr, foldl)


genericLength :: Enum i => Foldable t => t a -> i
genericLength = foldl (const . succ) (toEnum 0)

length :: Foldable t => t a -> Int
length = foldl (const . succ) 0

lookup :: (Foldable t, Eq a) => a -> t (a, b) -> Maybe b
lookup x = fmap snd . find ((x==) . fst)

substitute :: (Foldable t, Eq a, Functor f) => t (a, a) -> f a -> f a
substitute interpretation = fmap sub
    where sub x = case lookup x interpretation of
	    Nothing -> x
	    Just y -> y

substituteIx :: (Ix i, Functor f) => Array i i -> f i -> f i
substituteIx interpretation = fmap $ \x -> if inRange (bounds interpretation) x then interpretation ! x else x

-- allows replacement by constants as well
genericReplace :: (Foldable t, Eq a, Functor m, Monad m) => t (a, Either a (m a)) -> m a -> m a
genericReplace interpretation = join . fmap sub
    where sub x = case lookup x interpretation of
	    Nothing -> return x
	    Just (Left y) -> return y
	    Just (Right y) -> y

replace :: (Ix i, Functor m, Monad m) => Array i (Either i (m i)) -> m i -> m i
replace interpretation = join . fmap (\x -> if not $ inRange (bounds interpretation) x then return x else case interpretation ! x of
	Left y -> return y
	Right y -> y)

getVars :: (Foldable t, Ord a) => t a -> Set a
getVars = foldr insert empty
