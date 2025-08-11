module Algebra.Field where

import Algebra.RootField
import Algebra.DepTypes
import Algebra.FField

data Field =
  FAdd Field Field |
  FSub Field Field |
  FMult Field Field |
  FInv Field |
  FIntConst Int |
  FOne |
  -- FUndefined Field | -- isn't used, only for Num instance 
  FZero deriving (Eq,Ord)

instance Show Field where
  show (FAdd x y) = show x++"f+"++show y
  show (FSub x y) = show x++"f-"++show y
  show (FMult x y) = show x++"f*"++show y
  show (FInv x) = "f1/"++show x
  show (FIntConst x) = show x
  show FOne = "f1"
  show FZero = "f0"

instance DepType ModPrimeMemo Field where
  is_instance mpm f = True
  
instance HasIntEmb ModPrimeMemo Field where
  _get_int_emb mpm (FAdd x y) = mod ((get_int_emb mpm x) + (get_int_emb mpm y)) (prime mpm)
  _get_int_emb mpm (FSub x y) = mod ((get_int_emb mpm x) - (get_int_emb mpm y)) (prime mpm)
  _get_int_emb mpm (FMult x y) = mod ((get_int_emb mpm x) * (get_int_emb mpm y)) (prime mpm)
  _get_int_emb mpm (FInv y) = field_inverse mpm (get_int_emb mpm y)
  _get_int_emb mpm (FIntConst i) = mod i (prime mpm)
  _get_int_emb mpm FOne = 1
  _get_int_emb mpm FZero = 0

  -- instance Num Field where
--   (+) = field_simpl . FAdd
--   (*) = field_simpl . FMult
--   (-) = field_simpl . FSub
--   abs = FUndefined
--   signum = FUndefined
--   fromInteger = FIntConst
  
type FieldTimesROU = (Field,RootOfUnity)

instance {-# OVERLAPS #-} Show FieldTimesROU where
  show (FOne,rou) = show rou
  show (FZero,_) = "."
  show (f,rou) = show f++"*"++show rou

dist_pair :: (a -> a -> a) -> (b -> b -> b) -> (a,b) -> (a,b) -> (a,b)
dist_pair aop bop (a0,b0) (a1,b1) = (aop a0 a1,bop b0 b1)

-- instance Num FieldTimesROU where
--   (+) dist_pair (f0,r0) ‘+’, ‘*’, ‘abs’, ‘signum’, ‘fromInteger’, and (either ‘negate’

fieldxrou_mult :: FieldTimesROU -> FieldTimesROU -> FieldTimesROU
fieldxrou_mult (f0, r0) (f1, r1) = (field_simpl (FMult f0 f1), ru_mult r0 r1)
                                                            
field_simpl :: Field -> Field
field_simpl (FAdd FZero a) = field_simpl a
field_simpl (FAdd a FZero) = field_simpl a
field_simpl (FSub a FZero) = field_simpl a
field_simpl (FMult FOne a) = field_simpl a
field_simpl (FMult a FOne) = field_simpl a
field_simpl (FMult a FZero) = FZero
field_simpl (FMult FZero a) = FZero
field_simpl (FInv FOne) = FOne
field_simpl f = f
            
fxr_zero :: NthRoots -> FieldTimesROU
fxr_zero (NR n) = (FZero,RU n 0)

fxr_one :: NthRoots -> FieldTimesROU
fxr_one (NR n) = (FOne,RU n 0)

instance HasIntEmb (DPair ModPrimeMemo ModPrimeMemo) FieldTimesROU where
  _get_int_emb (DPair mpm0 mpm1) (f,ru) =
    let mpm = reconcile_mpm_instances mpm0 mpm1 in
      reduce mpm (get_int_emb mpm f * get_int_emb mpm ru)

instance HasFFieldEmb ModPrimeMemo RootOfUnity where
  _get_ffield_emb mpm ru = FF mpm (get_int_emb mpm ru)

instance HasFFieldEmb (DPair ModPrimeMemo ModPrimeMemo) FieldTimesROU where
  _get_ffield_emb (DPair mpm0 mpm1) (f,ru) =
    let mpm = reconcile_mpm_instances mpm0 mpm1 in
      FF mpm (reduce mpm (get_int_emb mpm f * get_int_emb mpm ru))

instance HasFFieldEmb ModPrimeMemo Int where
  _get_ffield_emb mpm n = FF mpm (reduce mpm n)
