module Algebra.Stencil where

import Algebra.NTT
import Algebra.FField
import Algebra.DepTypes

import Control.Monad

convolution_mat :: [a] -> LinearOp a
convolution_mat vec =
  let
    n=length vec
  in
    linearOp n (\(x,y) -> vec !! (mod (y-x) n))

ff_conv :: ModPrimeMemo -> [Int] -> LinearOp FField
ff_conv mpm vec = fmap (get_ffield_emb mpm) $ convolution_mat vec

project_sub :: ModPrimeMemo -> Int -> Int -> LinearOp FField
project_sub mpm k n = linearOp n (\(x,y) -> get_ffield_emb mpm ((if x==y && x < k then 1 else 0) :: Int))

-- test
mpm8 = init_ModPrimeMemo 17 8
conv8 = (ff_conv mpm8 [1,2,1,0,0,0,0,0])
ntt8 = fmap (get_ffield_emb mpm8) (mNTT 8)
ntt8_inv = fmap (get_ffield_emb (DPair mpm8 mpm8)) (mNTT_inv 8)

mpm4 = init_ModPrimeMemo 5 4
ntt4_inv = fmap (get_ffield_emb (DPair mpm4 mpm4)) (mNTT_inv 4)
ntt4_inv_2 = ntt4_inv * ntt4_inv
ntt4 = fmap (get_ffield_emb mpm4) (mNTT 4)
ntt4_2 = ntt4 * ntt4

mpm2 = init_ModPrimeMemo 5 2
ntt2_inv = fmap (get_ffield_emb (DPair mpm2 mpm2)) (mNTT_inv 2)
ntt2 = fmap (get_ffield_emb mpm4) (mNTT 2)

conv4 = (ff_conv mpm4 [0,1,2,1])
s_diag = ntt4 * conv4 * ntt4_inv
rho_S_diag = ntt4_2 * (project_sub mpm4 2 4) * ntt4_inv_2 * ntt4_2 * conv4 * ntt4_inv_2

ntt4_wrapper n x = foldl (*) (foldr (*) x [ntt4 | i<-[0..n-1]]) [ntt4_inv | i<-[0..n-1]]

lo_field_emb mpm = fmap (get_ffield_emb (DPair mpm mpm))
-- phi_lo :: Int -> Int -> Int -> Int -> LinearOp FieldTimesROU
phi_lo n k d b = linearOp n . uncurry $ phi_func_memo n k d b

phi_inv_lo n k d b = linearOp n . uncurry $ phi_inv_func_memo n k d b

phi_wrapper p n k d b mpm x =
  let
    phi_mat = lo_field_emb mpm (phi_lo n k d b)
    phi_inv_mat = lo_field_emb mpm (phi_inv_lo n k d b)
  in
    (mm_exp p phi_mat) * x * (mm_exp p phi_inv_mat)
    
is_diagonal :: Eq a => a -> LinearOp a -> Bool
is_diagonal zero lo =
  all id . join $ do
    let n = size lo
    x <- [0..n-1]
    return $ do
      y <- [0..n-1]
      let el = get_el x y lo
      return $ if x /= y && el /= zero then False else True
