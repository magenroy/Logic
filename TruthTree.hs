module TruthTree where

import Propositional
import Prelude hiding (foldr, lookup, null, length)
import Data.Foldable
import Data.Monoid
import Data.Array
import Control.Applicative (Applicative, pure, (<*>))
import Data.List (nub)
import Data.Set hiding (toList, foldr, map)
import Data.Maybe (fromJust)

import Abstractions (lookup)

data TruthTree a = Value Bool | Interpret {name :: a, false :: TruthTree a, true :: TruthTree a} deriving (Eq, Ord, Show, Read)

data TruthPath = Stop | Choose (Either TruthPath TruthPath) deriving (Eq, Ord, Show, Read) -- Left means F, Right means T

climb :: TruthTree a -> TruthPath -> TruthTree a
climb v@(Value _) _ = v
climb t Stop = t
climb t (Choose (Left path)) = climb (false t) path
climb t (Choose (Right path)) = climb (true t) path

instance Foldable TruthTree where
    foldMap _ (Value _) = mempty
    foldMap fn (Interpret n f t) = foldMap fn f <> fn n <> foldMap fn t

genericChop :: (Eq a, Foldable t) => TruthTree a -> t (a, Bool) -> TruthTree a
genericChop v@(Value _) _ = v
genericChop (Interpret n f t) assocs = case lookup n assocs of -- should remove (n, v) from assocs
    Nothing -> Interpret n (genericChop f assocs) (genericChop t assocs)
    Just v -> if v then genericChop t assocs else genericChop f assocs

chop :: Ix i => TruthTree i -> Array i Bool -> TruthTree i
chop v@(Value _) _ = v
chop (Interpret n f t) arr = if inRange (bounds arr) n
    then if arr ! n then chop t arr else chop f arr
    else Interpret n (chop f arr) (chop t arr)

trimTruthTree :: Eq a => TruthTree a -> TruthTree a
trimTruthTree v@(Value _) = v
trimTruthTree (Interpret n f t) = let (goF, goT) = (trimTruthTree f, trimTruthTree t) in if goF == goT then goF else Interpret n goF goT

leafs :: (Monoid (f Bool), Applicative f) => TruthTree a -> f Bool
leafs (Value v) = pure v
leafs (Interpret _ f t) = leafs f <> leafs t

genericTrimTruthTree :: TruthTree a -> TruthTree a
genericTrimTruthTree v@(Value _) = v
genericTrimTruthTree tree = case nub $ leafs tree of
    [v] -> Value v -- if all paths evaluate to the same value
    _ -> tree{false = genericTrimTruthTree $ false tree, true = genericTrimTruthTree $ true tree}

-- is it possible to make a version without Eq?
genericPropToTree :: Eq a => Proposition a -> TruthTree a
genericPropToTree F = Value False
genericPropToTree T = Value True
genericPropToTree (Atom v) = Interpret v (genericPropToTree F) (genericPropToTree T)
genericPropToTree p = case toList p of -- put non empty case first since will have to traverse entire p to check if empty
    (v:_) -> Interpret v (genericPropToTree $ sub1 v F p) (genericPropToTree $ sub1 v T p)
    [] -> Value $ fromJust $ interpret p empty

genericPropToTrimmedTree :: Eq a => Proposition a -> TruthTree a
genericPropToTrimmedTree F = Value False
genericPropToTrimmedTree T = Value True
genericPropToTrimmedTree (Atom v) = Interpret v (genericPropToTrimmedTree F) (genericPropToTrimmedTree T)
genericPropToTrimmedTree prop = let p = simplify prop in case toList p of -- simplify at beginning of each recursive call
    (v:_) -> Interpret v (genericPropToTrimmedTree $ sub1 v F p) (genericPropToTrimmedTree $ sub1 v T p)
    [] -> Value $ fromJust $ interpret p empty

-- maybe should also make a sortTree function...

-- makes sorted tree
propToTree :: Ord a => Proposition a -> TruthTree a
propToTree prop = go prop $ getVars prop -- don't need to put non-empty case first since don't need to traverse p
    where go p vars = case minView vars of
	    Nothing -> Value $ fromJust $ interpret p empty
	    Just (v, vs) -> Interpret v (go (sub1 v F p) vs) (go (sub1 v T p) vs)

propToTrimmedTree :: Ord a => Proposition a -> TruthTree a
propToTrimmedTree = go <*> getVars
    --where go prop vars = let p = simplify prop in case 
    where go prop vars | not $ null $ intersection vars $ getVars p = -- make this less horribly inefficient (and neater)
			    let (v,vs) = deleteFindMin vars
			    in Interpret v (go (sub1 v F p) vs) (go (sub1 v T p) vs)
		       | otherwise = Value $ fromJust $ interpret p empty
		       where p = simplify prop

treeToProp (Value False) = F
treeToProp (Value True) = T
treeToProp (Interpret p q r) = ifThenElse (Atom p) (treeToProp r) (treeToProp q)

boolsToPath :: Foldable t => t Bool -> TruthPath
boolsToPath = foldr (\x -> Choose . if x then Right else Left) Stop

pathToBools :: TruthPath -> [Bool]
pathToBools Stop = []
pathToBools (Choose (Left path)) = False:pathToBools path
pathToBools (Choose (Right path)) = True:pathToBools path

-- this is here temporarily
-- it doesn't work properly (doesn't terminate)
truthTable p = let n = length p
		   bnds = (Indices $ replicate n False, Indices $ replicate n True)
	       in listArray bnds $ map (climb $ propToTree p) $ map boolsToPath $ range bnds


--interpretationToPath will require Ord to predict order

--treeToTable

--tableToTree
