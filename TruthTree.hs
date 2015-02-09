import Propositional
import Data.Foldable

data TruthTree a = Value Bool | Interpret {name :: a, false :: TruthTree a, true :: TruthTree a}

data TruthPath = Stop | Choose (Either TruthPath TruthPath) -- Left means F, Right means T

climb :: TruthTree a -> TruthPath -> Either (TruthTree a) Bool
climb (Value r) _ = Right r
climb t Stop = Left t
climb t (Choose (Left path)) = climb (false t) path
climb t (Choose (Right path)) = climb (true t) path

-- make a function that takes a TruthTree and an associative collection that
-- does something similar to climb (does not have to predict order of variables)
-- seems like I might have to implement Foldable TruthTree...

chop :: Foldable t => TruthTree a -> t (a, Bool) -> Either (TruthTree a) Bool
chop (Value r) _ = Right r
