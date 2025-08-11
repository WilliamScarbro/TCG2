module Algebra.RootField where

-- abstracts roots of unity (everything is a root of unity)
import Algebra.DepTypes


data RootOfUnity = RU Int Int deriving Eq -- \omega n ^ k

ru_reduce (RU n k) = (RU n (mod k n))

ru_init n k = ru_reduce (RU n k)

ru_is_one (RU n k) = mod k n == 0

ru_mult (RU n0 k0) (RU n1 k1) | n0 == n1 = (RU n0 (k0+k1))
                              | otherwise = error "cannot multiply roots of unit with different bases (requires extended euclidean algorithm)"
                                           
instance Show RootOfUnity where
  show (RU n k) | ru_is_one (RU n k) = "{1}"
                | mod k n == div n 2 = "{-1}"
                | otherwise = "{w_"++show n++"^"++show k++"}"

data NthRoots = NR Int deriving (Show,Eq)

instance DepType NthRoots RootOfUnity where
  is_instance (NR n0) (RU n1 k) = n0 == n1
  
class CyclicGroup a b where
  cyc_id :: a -> b
  cyc_add :: a -> b -> b -> b

instance CyclicGroup NthRoots RootOfUnity where
  cyc_id (NR n) = (RU n 1)
  cyc_add (NR n) (RU n0 k0) (RU n1 k1) | n == n0 && n0 == n1 = ru_init n (k0 + k1) 
                                       | otherwise = error ("attempted to add roots of unity with different bases") -- requires Extended Euclidian Algorithm (changes cyclic group)

class RootField a b where
  find_root_power :: a -> RootOfUnity -> b


  
-- get_root_power :: ModPrimeMemo -> Int -> Int
-- get_root_power mpm e = (root_power_table mpm) !! (mod e (n mpm))


-- test

type NRcap0 = DEither NthRoots Zero
type ROUcap0 = Either RootOfUnity Zero

instance {-# OVERLAPS #-} Show ROUcap0 where
  show (Left ru) = show ru
  show (Right Zero) = "{0}"

-- first Zero should really be a type representing all Zero... 
instance DepType Zero Zero where
  is_instance _ _ = True
  
instance Has01 NRcap0 ROUcap0 where
  get_zero _ = Right Zero
  get_one (DEither (NR n) _) = Left (ru_init n 1)


-- instance Num RootOfUnity where
--   (+) = field_simpl . FAdd
--   (*) = field_simpl . FMult
--   (-) = field_simpl . FSub
--   abs = FUndefined
--   signum = FUndefined
--   fromInteger = FIntConst
