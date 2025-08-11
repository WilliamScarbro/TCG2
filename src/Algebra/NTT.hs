{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Algebra.NTT where

import Algebra.FField -- ModPrimeMemo and IntField
import Algebra.RootField
import Algebra.DepTypes
import Algebra.Field
-- import Algebra.PolyRings
-- import qualified Algebra.BetterAlgebra as BA

import Data.Matrix


data LinearOp a where
  LO :: (Matrix a) -> LinearOp a

data Vector a where
  Vec :: (Matrix a) -> Vector a
  deriving Eq
  

vecAsList :: Vector a -> [a]
vecAsList (Vec m) =
  if ncols m == 1 then
    [get_vec_el i 0 (Vec m) | i <- [0..(nrows m - 1)]]
  else
    [get_vec_el 0 i (Vec m) | i <- [0..(ncols m - 1)]]
    
-- cannon_ffVec n p = ffVec n p id

linearOp :: Integral a => a -> ((Int,Int)->b) -> LinearOp b
linearOp n f = LO (matrix (fromIntegral n) (fromIntegral n) (\(x,y) -> f ((x-1),(y-1))))

vector n f = Vec (matrix n 1 (\(x,y) -> f (x - 1)))

-- haskell matrices are 1 indexed :\
get_el :: Int -> Int -> LinearOp a -> a
get_el x y (LO m) = getElem (x+1) (y+1) m

get_vec_el :: Int -> Int -> Vector a -> a
get_vec_el x y (Vec m) = getElem (x+1) (y+1) m

size :: LinearOp a -> Int
size (LO m) = nrows m

----


lo_op :: (Matrix a -> Matrix a -> Matrix a) -> (LinearOp a -> LinearOp a -> LinearOp a)
lo_op op (LO x) (LO y) = LO (op x y)

lo_cmp :: (Matrix a -> Matrix a -> Bool) -> (LinearOp a -> LinearOp a -> Bool)
lo_cmp op (LO x) (LO y) = op x y


instance Foldable LinearOp where
  foldMap f (LO m) = foldMap f m
  foldr f b (LO m) = foldr f b m
  
instance Show a => Show (LinearOp a) where
  show (LO m) = show m

instance Show a => Show (Vector a) where
  show (Vec v) = show v

instance Functor LinearOp where
  -- (a->b) -> (f a->f b) = 
  fmap f (LO m) = LO (fmap f m)

instance Functor Vector where
  fmap f (Vec m) = Vec (fmap f m)
  
instance (Num a) => Num (LinearOp a) where
  (+) = lo_op (+)
  negate = fmap negate
  (-) = lo_op (-)
  (*) = lo_op (*)
  abs = error "abs not defined for LinearOp" 
  signum x = error "signum not defined for LinearOp"
  fromInteger x = error "fromInteger not defined for LinearOp" -- linearOp 1 (\(z,y) -> fromInteger x)

instance Eq a => Eq (LinearOp a) where
  (==) = lo_cmp (==)


lopToInteger :: HasIntEmb context a => context -> LinearOp a -> LinearOp Int
lopToInteger context lo = fmap (get_int_emb context) lo

---

mm :: Num a => LinearOp a -> LinearOp a -> LinearOp a
mm (LO m) (LO m2) | nrows m /= ncols m2 = error "mm: dimension mismatch"
                  | otherwise = LO (m * m2)

my_mm :: Num a => LinearOp a -> LinearOp a -> LinearOp a
my_mm (LO m) (LO m2) | ncols m /= nrows m2 = error "mm: dimension mismatch"
                  | otherwise =
  linearOp (ncols m) (\(x,y) -> foldr (+) 0 [(get_el x i (LO m)) * (get_el i y (LO m2)) | i<-[0..(ncols m)-1]])

mv :: Num a => LinearOp a -> Vector a -> Maybe (Vector a)
mv (LO m) (Vec v) | ncols m /= nrows v = Nothing
                  | otherwise = Just (Vec (m*v))

vm :: Num a => Vector a -> LinearOp a -> Maybe (Vector a)
vm (Vec v) (LO m) | ncols v /= nrows m = Nothing
                  | otherwise = Just (Vec (v*m))

vv :: Num a => Vector a -> Vector a -> Maybe (Vector a)
vv (Vec v) (Vec v2) | ncols v /= nrows v2 = Nothing
                    | otherwise = Just (Vec (v*v2))

point_mult :: Num a => Vector a -> Vector a -> Maybe (Vector a)
point_mult (Vec v1) (Vec v2) | nrows v1 /= nrows v2 = Nothing
                             | ncols v1 /= ncols v2 = Nothing
                             | nrows v1 /= 1 =
                               return (Vec (matrix (nrows v1) 1 (\(i,j) -> (getElem i 1 v1)*(getElem i 1 v2))))
                             | ncols v1 /= 1 =
                               return (Vec (matrix 1 (ncols v1) (\(i,j) -> (getElem 1 j v1)*(getElem 1 j v2))))
                                   

mm_exp :: Num a => Int -> LinearOp a -> LinearOp a
mm_exp n lo = foldr (mm) lo [lo |i<-[1..n-1]]

tensor :: (a -> a -> a) -> LinearOp a -> LinearOp a -> LinearOp a
tensor mult l1 l2 =
  let
    n1=size l1
    n2=size l2
  in
  linearOp (n1 * n2) (\(x,y) ->  mult (get_el (div x n2) (div y n2) l1) (get_el (mod x n2) (mod y n2) l2))

tpose :: LinearOp a -> LinearOp a
tpose l = linearOp (size l) (\(x,y) -> get_el y x l)

vtpose :: Vector a -> Vector a
vtpose (Vec m) = Vec (matrix (ncols m) (nrows m) (\(x,y) -> getElem y x m))

loParallel :: a -> LinearOp a -> LinearOp a -> LinearOp a
loParallel zero l1 l2 =
  let
    n1 = size l1
    n2 = size l2
  in
    linearOp (n1 + n2) (\(x,y) -> (
                           if x < n1 && y < n1 then
                             get_el x y l1
                           else
                             if x >= n1 && y >= n1 then
                               get_el (x-n1) (y-n1) l2
                             else
                               zero))
 
mult_lo_seq :: Num a => [LinearOp a] -> LinearOp a
mult_lo_seq (lo:[]) = lo
mult_lo_seq (lo:los) = foldl mm lo los


lo_pointwise_op :: (a -> b -> c) -> LinearOp a -> LinearOp b -> LinearOp c
lo_pointwise_op f lo1 lo2 | size lo1 /= size lo2 = error "pointwise_op: dim mismatch"
                       | otherwise = linearOp (size lo1) (\(x,y) -> f (get_el x y lo1) (get_el x y lo2))
                       
---------
   
mId :: a -> a -> Int -> LinearOp a
mId zero one n = linearOp n (\(i,j) -> if i==j then one else zero)

-- assumes (Int -> Int) is a bijection
perm :: Has01 a b => a -> Int -> (Int -> Int) -> LinearOp b
perm typ n f = linearOp n (\(i,j) -> if f (j)==i then (get_one typ) else (get_zero typ))

mT_perm :: Int -> Int -> Int -> Int -> Int
mT_perm di dj dk x =
  let
    i = div x (dj*dk)
    j = div (mod x (dj*dk)) dk
    k = mod x dk in
  (di*dk) * j + dk * i + k
   
  
mT :: Has01 a b => a -> Int -> Int -> Int -> LinearOp b
mT typ di dj dk = perm typ (di*dj*dk) (mT_perm di dj dk)

mL_perm :: Int -> Int -> Int -> Int
mL_perm n k x = let m = fromIntegral (div n k) in let ik = fromIntegral k in (div x ik) + m * (mod x ik)

mL :: Has01 a b => a -> Int -> Int -> LinearOp b
mL typ n k = perm typ n (mL_perm n k)


---

mNTT :: Int -> LinearOp RootOfUnity
mNTT n = linearOp n (\(i,j) -> ru_init n (i*j))
 
mNTT_inv ::  Int -> LinearOp FieldTimesROU
mNTT_inv n =
  linearOp n (\(i,j) -> (FInv (FIntConst n), ru_init n (-1*i*j)))

phi_func_memo :: Int -> Int -> Int -> Int -> Int -> Int -> FieldTimesROU
phi_func_memo n k d b =
  let
    rd = mod d b
    m = div n k
  in
    (\y x ->
       if mod x m == mod y m then
         (FOne,ru_init b (div ((rd+(div x m)*b)*(div y m)) k))
         else
         fxr_zero (NR b))


phi_inv_func_memo :: Int -> Int -> Int -> Int -> Int -> Int -> FieldTimesROU
phi_inv_func_memo n k d b =
  let
    rd = mod d b
    m = div n k
    k_inv = FInv (FIntConst k)
  in
    (\y x ->
       if mod x m == mod y m then
         (k_inv,ru_init b (-(div ((rd+(div x m)*b)*(div y m)) k)))
         else
         fxr_zero (NR b))

psi_func_memo :: Int -> Int -> Int -> Int -> Int -> FieldTimesROU
psi_func_memo k m d b x = (FOne,ru_init b ((div d k)*(div x m)))


psi_inv_func_memo :: Int -> Int -> Int -> Int -> Int -> FieldTimesROU
psi_inv_func_memo k m d b x = (FOne,ru_init b (-(div d k)*(div x m)))

        
-----


