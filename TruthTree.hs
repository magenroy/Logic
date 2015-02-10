-- an interesting idea



import Propositional
import Abstractions
import Prelude hiding (foldr, lookup)
import Data.Foldable
import Data.Monoid
import Data.Array
import Control.Applicative
import Data.List (nub)

data TruthTree a = Value Bool | Interpret {name :: a, false :: TruthTree a, true :: TruthTree a} deriving (Eq, Ord, Show, Read)

data TruthPath = Stop | Choose (Either TruthPath TruthPath) -- Left means F, Right means T

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
trimTruthTree tree@(Interpret _ f t) = let go = trimTruthTree f in if go == trimTruthTree t then go else tree

leafs :: (Monoid (f Bool), Applicative f) => TruthTree a -> f Bool
leafs (Value v) = pure v
leafs (Interpret _ f t) = leafs f <> leafs t

genericTrimTruthTree :: TruthTree a -> TruthTree a
genericTrimTruthTree v@(Value _) = v
genericTrimTruthTree tree@(Interpret _ f t) = case nub $ leafs f <> leafs t of
    [v] -> Value v -- if all paths evaluate to the same value
    _ -> tree

--interpretationToPath will require Ix to predict order

--genTruthTree

--treeToTable

--tableToTree

--treeToProp
