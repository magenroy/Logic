{-# LANGUAGE ConstraintKinds, MultiParamTypeClasses #-}
module Propositional (
    Proposition(..),
    (&.),
    (|.),
    implies,
    (-->),
    implied,
    (<--),
    iff,
    (<-->),
    nor,
    nand,
    xor,
    ifThenElse,
    genericLength,
    length,
    get,
    apply,
    applyA,
    applyM,
    genericSubPropositions,
    subPropositions,
    commute,
    associate,
    permutations,
    genericSimplifyTop,
    simplifyTop,
    genericSimplify,
    simplify,
    toNNF,
    deMorgan,
    substitute,
    substituteMap,
    substituteIx,
    replace,
    replaceMap,
    replaceIx,
    sub1,
    getVars,
    interpret,
    interpretMap,
    interpretIx,
    interpretationMaps,
    truthTable,
    truthMap,
    truthArray,
    distributeAllTop,
    distributeAll,
    distributeOrTop,
    distributeOr,
    distributeAndTop,
    distributeAnd,
    toCNF,
    toDNF
) where

-- maybe I can fix the repetitiveness of "generic version, map version, array
-- version" by making a lookup typeclass
-- but then I need to be able to place constraints on the type of keys
-- consider solution with ConstraintKinds and MultiParamTypeClasses

import Prelude hiding (map, lookup, foldr, foldl, length)
import Data.Traversable
import Data.Monoid
import Control.Applicative (Applicative, pure, (<*>), liftA2, liftA3)
import Control.Monad
import Data.Foldable (find, Foldable, foldMap, fold, foldr, foldl, toList)
import qualified Data.List as List (nub, permutations)
import Data.Maybe (fromJust, isJust)
import Data.Array
import Data.Set hiding (fold, foldr, foldl, toList)
import qualified Data.Map as Map

data Proposition a = F | T | Atom a | Not (Proposition a) | Or (Proposition a) (Proposition a) | And (Proposition a) (Proposition a) deriving (Eq, Ord, Show, Read)


infixr 3 &.
infixr 2 |.
infixr -->
infixl <--
infix <-->
(&.), (|.), implies, (-->), implied, (<--), iff, (<-->), nor, nand, xor :: Proposition a -> Proposition a -> Proposition a

(&.) = And
(|.) = Or

implies = Or . Not
(-->) = implies

implied = flip implies
(<--) = implied

iff a b = implies a b &. implies b a
(<-->) = iff

nor a b = Not (a |. b)
nand a b = Not (a &. b)
xor = iff . Not

ifThenElse :: Proposition a -> Proposition a -> Proposition a -> Proposition a
ifThenElse p q r = implies p q &. Or p r


-- these should be semantic versions of above
--entails, (==>), entailed, (<==), equiv, (<==>) :: Proposition a -> Proposition a -> Bool

instance Functor Proposition where
    fmap _ F = F
    fmap _ T = T
    fmap f (Atom x) = Atom $ f x
    fmap f (Not p) = Not $ fmap f p
    fmap f (Or p q) = fmap f p |. fmap f q
    fmap f (And p q) = fmap f p &. fmap f q

instance Applicative Proposition where
    pure = Atom
    F <*> _ = F
    T <*> _ = T
    Atom f <*> p = fmap f p
    Not f <*> p = Not $ f <*> p
    Or f g <*> p = Or (f <*> p) (g <*> p)
    And f g <*> p = And (f <*> p) (g <*> p)

instance Monad Proposition where
    return = pure
    F >>= _ = F
    T >>= _ = T
    Atom v >>= f = f v
    Not p >>= f = Not $ p >>= f
    Or p q >>= f = Or (p >>= f) (q >>= f)
    And p q >>= f = And (p >>= f) (q >>= f)

instance Foldable Proposition where
    foldr _ acc F = acc
    foldr _ acc T = acc
    foldr f acc (Atom v) = f v acc
    foldr f acc (Not p) = foldr f acc p
    foldr f acc (Or p q) = foldr f (foldr f acc p) q
    foldr f acc (And p q) = foldr f (foldr f acc p) q

instance Traversable Proposition where
    traverse _ F = pure F
    traverse _ T = pure T
    traverse f (Atom x) = fmap Atom $ f x
    traverse f (Not p) = fmap Not $ traverse f p
    traverse f (Or p q) = liftA2 Or (traverse f p) (traverse f q)
    traverse f (And p q) = liftA2 And (traverse f p) (traverse f q)

class Lookup l constr where
    look :: constr a => a -> l a b -> Maybe b

newtype Look t a b = Look {view :: (t (a, b))}

instance Foldable t => Lookup (Look t) Eq where
    look x = fmap snd . find ((x==) . fst) . view

instance Lookup Map.Map Ord where
    look = Map.lookup

instance Lookup Array Ix where
    look x arr = if inRange (bounds arr) x then Just $ arr ! x else Nothing

genericLength :: Enum i => Foldable t => t a -> i
genericLength = foldl (const . succ) (toEnum 0)

length :: Foldable t => t a -> Int
length = foldl (const . succ) 0

get :: Proposition a -> Maybe (Either a (Proposition a, Proposition a))
get F = Nothing
get T = Nothing
get (Atom v) = Just $ Left v
get (Or p q) = Just $ Right (p,q)
get (And p q) = Just $ Right (p,q)

apply :: (Proposition a -> Proposition a) -> Proposition a -> Proposition a
apply _ F = F
apply _ T = T
apply _ p@(Atom _) = p
apply f (Not p) = Not $ f p
apply f (Or p q) = Or (f p) (f q)
apply f (And p q) = And (f p) (f q)

applyA :: Applicative f => (Proposition a -> f (Proposition a)) -> Proposition a -> f (Proposition a)
applyA _ F = pure F
applyA _ T = pure T
applyA _ p@(Atom _) = pure p
applyA f (Not p) = fmap Not $ f p
applyA f (Or p q) = liftA2 Or (f p) (f q)
applyA f (And p q) = liftA2 And (f p) (f q)

applyM :: Monad m => (Proposition a -> m (Proposition a)) -> Proposition a -> m (Proposition a)
applyM _ F = return F
applyM _ T = return T
applyM _ p@(Atom _) = return p
applyM f (Not p) = liftM Not $ f p
applyM f (Or p q) = liftM2 Or (f p) (f q)
applyM f (And p q) = liftM2 And (f p) (f q)

genericSubPropositions :: Proposition a -> [Proposition a]
genericSubPropositions x@(Or p q) = x:genericSubPropositions p ++ genericSubPropositions q
genericSubPropositions x@(And p q) = x:genericSubPropositions p ++ genericSubPropositions q
genericSubPropositions p = [p]

subPropositions :: Ord a => Proposition a -> Set (Proposition a)
subPropositions x@(Or p q) = insert x $ union (subPropositions p) (subPropositions q)
subPropositions x@(And p q) = insert x $ union (subPropositions p) (subPropositions q)
subPropositions p = singleton p

commute :: Proposition a -> Proposition a
commute (Or p q) = Or q p
commute (And p q) = And q p
commute p = p

commutable :: Proposition a -> Bool
commutable (Or _ _) = True
commutable (And _ _) = True
commutable _ = False

associate :: Proposition a -> Proposition a
associate (Or (Or p q) r) = Or p (Or q r)
associate (Or p (Or q r)) = (Or (Or p q) r)
associate (And (And p q) r) = And p (And q r)
associate (And p (And q r)) = (And (And p q) r)
associate p = p

associable :: Proposition a -> Bool
associable (Or (Or _ _) _) = True
associable (Or _ (Or _ _)) = True
associable (And (And _ _) _) = True
associable (And _ (And _ _)) = True
associable _ = False

-- this only works as expected for lists (come up with a better name)
permutations :: (Monad m, Monoid (m (Proposition a))) => Proposition a -> m (Proposition a)
permutations p = return p <> ((if commutable p then return (commute p) else mempty) <> (if associable p then return (associate p) else mempty)) >>= applyM permutations

genericSimplifyTop :: Proposition a -> Proposition a
genericSimplifyTop (Not F) = T
genericSimplifyTop (Not T) = F
genericSimplifyTop (Not (Not p)) = p
genericSimplifyTop (Or T _) = T
genericSimplifyTop (Or _ T) = T
genericSimplifyTop (Or F F) = F
genericSimplifyTop (Or F p) = p
genericSimplifyTop (Or p F) = p
genericSimplifyTop (And F _) = F
genericSimplifyTop (And _ F) = F
genericSimplifyTop (And T T) = T
genericSimplifyTop (And T p) = p
genericSimplifyTop (And p T) = p
genericSimplifyTop p = p

simplifyTop :: Eq a => Proposition a -> Proposition a
simplifyTop (Not F) = T
simplifyTop (Not T) = F
simplifyTop (Not (Not p)) = p
simplifyTop (Or T _) = T
simplifyTop (Or _ T) = T
simplifyTop (Or F F) = F
simplifyTop (Or F p) = p
simplifyTop (Or p F) = p
simplifyTop x@(Or p q) | p == q = p
		       | p == simplifyTop (Not q) = T
		       | otherwise = x
simplifyTop (And F _) = F
simplifyTop (And _ F) = F
simplifyTop (And T T) = T
simplifyTop (And T p) = p
simplifyTop (And p T) = p
simplifyTop x@(And p q) | p == q = p
		        | p == simplifyTop (Not q) = F
		        | otherwise = x
simplifyTop p = p

genericSimplify :: Proposition a -> Proposition a
genericSimplify = genericSimplifyTop . apply genericSimplify

simplify :: Eq a => Proposition a -> Proposition a
simplify = simplifyTop . apply simplify

-- recursively apply De Morgan laws
toNNF :: Proposition a -> Proposition a
toNNF (Not (Or p q)) = And (Not $ toNNF p) (Not $ toNNF q)
toNNF (Not (And p q)) = Or (Not $ toNNF p) (Not $ toNNF q)
toNNF p = p

-- apply De Morgan laws only at top level
deMorgan :: Proposition a -> Proposition a
deMorgan (Not (Or p q)) = And (Not p) (Not q)
deMorgan (Not (And p q)) = Or (Not p) (Not q)
deMorgan p = p

-- generalized lookup (why isn't this standard?)
lookup :: (Foldable t, Eq a) => a -> t (a, b) -> Maybe b
lookup x = fmap snd . find ((x==) . fst)

substitute :: (Foldable t, Eq a, Functor f) => t (a, a) -> f a -> f a
substitute interpretation = fmap sub
    where sub x = case lookup x interpretation of
	    Nothing -> x
	    Just y -> y

-- can this be made less repetitive?
substituteMap :: (Ord k, Functor f) => Map.Map k k -> f k -> f k
substituteMap interpretation = fmap sub
    where sub x = case Map.lookup x interpretation of
	    Nothing -> x
	    Just y -> y

substituteIx :: (Ix i, Functor f) => Array i i -> f i -> f i
substituteIx interpretation = fmap $ \x -> if inRange (bounds interpretation) x then interpretation ! x else x

-- allows replacement by constants as well
replace :: (Foldable t, Eq a, Functor m, Monad m) => t (a, (m a)) -> m a -> m a
replace interpretation = join . fmap (\x -> let y = lookup x interpretation in if isJust y then fromJust y else return x)

replaceMap :: (Ord k, Functor m, Monad m) => Map.Map k (m k) -> m k -> m k
replaceMap interpretation = join . fmap (\x -> let y = Map.lookup x interpretation in if isJust y then fromJust y else return x)

replaceIx :: (Ix i, Functor m, Monad m) => Array i (m i) -> m i -> m i
replaceIx interpretation = join . fmap (\x -> if inRange (bounds interpretation) x then interpretation ! x else return x)

sub1 :: (Functor m, Monad m, Eq a) => a -> m a -> m a -> m a
sub1 v w = replace [(v,w)]

getVars :: (Foldable t, Ord a) => t a -> Set a
getVars = foldr insert empty

interpret :: (Foldable t, Eq a) => Proposition a -> t (a, Bool) -> Maybe Bool
interpret F _ = Just False
interpret T _ = Just True
interpret (Atom v) t = lookup v t
interpret (Not p) t = fmap not $ interpret p t
interpret (Or p q) t = liftA2 (||) (interpret p t) (interpret q t)
interpret (And p q) t = liftA2 (&&) (interpret p t) (interpret q t)

interpretMap :: Ord a => Proposition a -> Map.Map a Bool -> Maybe Bool
interpretMap F _ = Just False
interpretMap T _ = Just True
interpretMap (Atom v) t = Map.lookup v t
interpretMap (Not p) t = fmap not $ interpretMap p t
interpretMap (Or p q) t = liftA2 (||) (interpretMap p t) (interpretMap q t)
interpretMap (And p q) t = liftA2 (&&) (interpretMap p t) (interpretMap q t)

interpretIx :: Ix i =>  Proposition i -> Array i Bool -> Maybe Bool
interpretIx F _ = Just False
interpretIx T _ = Just True
interpretIx (Atom v) t = if inRange (bounds t) v then Just $ t ! v else Nothing
interpretIx (Not p) t = fmap not $ interpretIx p t
interpretIx (Or p q) t = liftA2 (||) (interpretIx p t) (interpretIx q t)
interpretIx (And p q) t = liftA2 (&&) (interpretIx p t) (interpretIx q t)

-- this does not work as expected for all applicative f
truthTable :: (Monoid (f Bool), Applicative f, Eq a) => Proposition a -> f ([(a, Bool)], Bool)
truthTable prop = let ts = traverse (\var -> fmap ((,) var) $ pure False <> pure True) $ List.nub $ toList prop in fmap (liftA2 (,) id $ fromJust . interpret prop) ts

truthMap :: Ord a => Proposition a -> Map.Map [Bool] Bool
truthMap p = Map.mapKeysMonotonic Map.elems $ Map.fromSet (fromJust . interpretMap p) $ fromList $ interpretationMaps p

truthArray = undefined

-- this does not work as expected for all applicative f
interpretationMaps :: (Monoid (f Bool), Applicative f, Ord a) => Proposition a -> f (Map.Map a Bool)
interpretationMaps = sequenceA . Map.fromSet (const $ pure False <> pure True) . getVars
-- make generic and array version later

distributeAllTop :: Proposition a -> Proposition a
distributeAllTop p@(Not _) = deMorgan p
distributeAllTop p@(Or _ _) = distributeOrTop p
distributeAllTop p@(And _ _) = distributeAndTop p
distributeAllTop p = p

distributeAll :: Proposition a -> Proposition a
distributeAll (Not (Or p q)) = And (Not $ distributeAll p) (Not $ distributeAll q)
distributeAll (Not (And p q)) = Or (Not $ distributeAll p) (Not $ distributeAll q)
distributeAll (Or p (And q r)) = let p' = distributeAll p in And (Or p' (distributeAll q)) (Or p' (distributeAll r))
distributeAll (Or (And p q) r) = let r' = distributeAll r in And (Or (distributeAll p) r') (Or (distributeAll q) r')
distributeAll (And p (Or q r)) = let p' = distributeAll p in Or (And p' (distributeAll q)) (And p' (distributeAll r))
distributeAll (And (Or p q) r) = let r' = distributeAll r in Or (And (distributeAll p) r') (And (distributeAll q) r')
distributeAll p = p

distributeOrTop :: Proposition a -> Proposition a
distributeOrTop (Or p (And q r)) = And (Or p q) (Or p r)
distributeOrTop (Or (And p q) r) = And (Or p r) (Or q r)
distributeOrTop p = p

distributeOr :: Proposition a -> Proposition a
distributeOr (Or p (And q r)) = let p' = distributeOr p in And (Or p' (distributeOr q)) (Or p' (distributeOr r))
distributeOr (Or (And p q) r) = let r' = distributeOr r in And (Or (distributeOr p) r') (Or (distributeOr q) r')
distributeOr p = p

distributeAndTop :: Proposition a -> Proposition a
distributeAndTop (And p (Or q r)) = Or (And p q) (And p r)
distributeAndTop (And (Or p q) r) = Or (And p r) (And q r)
distributeAndTop p = p

distributeAnd :: Proposition a -> Proposition a
distributeAnd (And p (Or q r)) = let p' = distributeAnd p in Or (And p' (distributeAnd q)) (And p' (distributeAnd r))
distributeAnd (And (Or p q) r) = let r' = distributeAnd r in Or (And (distributeAnd p) r') (And (distributeAnd q) r')
distributeAnd p = p

-- should write all of these manipulations in terms of valid rules of inference
-- such as distributeOr etc

-- this might be wrong
toCNF :: Proposition a -> Proposition a
toCNF (Not (Or p q)) = And (Not $ toCNF p) (Not $ toCNF q)
toCNF (Not (And p q)) = Or (Not $ toCNF p) (Not $ toCNF q)
toCNF (Or p (And q r)) = let p' = toCNF p in And (Or p' (toCNF q)) (Or p' (toCNF r))
toCNF (Or (And p q) r) = let r' = toCNF r in And (Or (toCNF p) r') (Or (toCNF q) r')
toCNF p = p

-- this might be wrong
toDNF :: Proposition a -> Proposition a
toDNF (Not (Or p q)) = And (Not $ toDNF p) (Not $ toDNF q)
toDNF (Not (And p q)) = Or (Not $ toDNF p) (Not $ toDNF q)
toDNF (And p (Or q r)) = let p' = toDNF p in Or (And p' (toDNF q)) (And p' (toDNF r))
toDNF (And (Or p q) r) = let r' = toDNF r in Or (And (toDNF p) r') (And (toDNF q) r')
toDNF p = p
