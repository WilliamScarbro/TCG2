module Algebra.PolyRings where

import Algebra.Field
import Algebra.NTT
import Algebra.DepTypes
import Algebra.RootField
import Algebra.FField
import Algebra.Util
-- import Algebra.FField
-- import Algebra.NTT
-- import Util.Logger
-- import Util.Util

import Control.Exception
-- import Data.List
-- import Data.Maybe
-- import qualified Data.Map as Map (empty,insert,Map,member)
-- import System.Environment
import Control.Monad

data GenericExc = GE String deriving Show

instance Exception GenericExc

-----
-- Util

data BoundedNatFunc a = BNF Int (Int -> a)

bnf_to_list (BNF b f) = [f i | i<-[0..b-1]]

bnf_eval (BNF b f) i | i >=0 && i<b = f i
                     | otherwise = throw (GE "BNF eval error")
                     
infixl 2 @
(@)=bnf_eval
                     
instance Show a => Show (BoundedNatFunc a) where
  show bnf = show . fmap show . bnf_to_list $ bnf 

instance Eq a => Eq (BoundedNatFunc a) where
  (==) bnf1 bnf2 = (bnf_to_list bnf1) == (bnf_to_list bnf2)
  
--------


data Ring =
 Base Int Int Int Int | -- n d b p
 Prod Int Int (BoundedNatFunc Ring) | -- n k
 OExp Int Int Ring | -- outer expansion -- n k
 IExp Int Int Ring | -- inner expansion -- n k
 Rot Int Int Ring -- n d
 deriving (Show,Eq)


product_normal_form :: Ring -> Bool
product_normal_form (Base _ _ _ _) = True
product_normal_form (Prod n k bnf) = all id . fmap product_normal_form . bnf_to_list $ bnf
product_normal_form (OExp _ _ _) = False
product_normal_form (IExp _ _ _) = False
product_normal_form (Rot _ _ _) = False

get_root_order :: Ring -> [Int]
get_root_order (Base _ d _ _) = return d
get_root_order (Prod n k bnf) = join . fmap get_root_order . bnf_to_list $ bnf
get_root_order (OExp n k r) = [] -- should be in product_normal_form
get_root_order (IExp n k r) = [] -- dito
get_root_order (Rot n d r) = [] -- dito

get_root :: Ring -> Int
get_root (Base _ _ b _) =  b
get_root (Prod _ _ bnf) = get_root (bnf @ 0)
get_root (OExp _ _ r) = get_root r
get_root (IExp _ _ r) = get_root r
get_root (Rot _ _ r) = get_root r

get_prime :: Ring -> Int
get_prime (Base _ _ _ p) = p
get_prime (Prod _ _ bnf) =  get_prime (bnf @ 0)
get_prime (OExp _ _ r) = get_prime r
get_prime (IExp _ _ r) = get_prime r
get_prime (Rot _ _ r) = get_prime r

get_dim :: Ring -> Int
get_dim (Base n _ _ _) = n
get_dim (Prod n _ _) = n
get_dim (OExp n _ _) = n
get_dim (IExp n _ _) = n
get_dim (Rot n _ _) = n

------

data MorphismExc =
  FactorExc Int Ring |
  StrideExc Int Ring |
  ClumpExc Int Ring |
  NormExc Ring |
  DefineOExc Ring |
  DefineIExc Ring |
  DefineRExc Ring |
  SwapERExc Ring |
  SwapEPExc Ring |
  SwapRPExc Ring |
  JoinProdExc Ring |
  SwapJoinProdExc Ring deriving Show

instance Exception MorphismExc
  
-- phi
factor :: Int -> Ring -> Ring
factor k (Base n d b p) | mod n k == 0 = (Prod n k (BNF k (\i -> (Base (n `div` k) ((d `div` k)+i*(b `div` k)) b p))))
                        | otherwise = throw (FactorExc k (Base n d b p))
factor k r = throw (FactorExc k r)

--xi
stride :: Int -> Ring ->  Ring
stride k (Base n d b p) | mod n k == 0 = OExp n k (Base (n `div` k) d b p)
                       | otherwise    = throw (StrideExc k (Base n d b p))
stride k r = throw (StrideExc k r)

clump :: Int -> Ring ->  Ring
clump k (Base n d b p) | mod n k == 0 = IExp n k (Base (n `div` k) d b p)
                       | otherwise    = throw (ClumpExc k (Base n d b p))
clump k r = throw (ClumpExc k r)

--gamma
norm :: Ring -> Ring
norm (Base n d b p) | n /= 1 = (Rot n (div d n) (Base n 0 b p))
                    | otherwise = throw (NormExc (Base n d b p))
norm r = throw (NormExc r)

--psi
defineO :: Ring -> Ring
defineO (OExp n k (Base 1 d b p)) = (Base k d b p)
defineO r = throw (DefineOExc r)

defineI :: Ring -> Ring
defineI (IExp n k (Base 1 d b p)) = (Base k d b p)
defineI r = throw (DefineIExc r)

defineR :: Ring -> Ring
defineR (Rot 1 d0 (Base 1 d1 b p)) = (Base 1 (d0 + d1) b p)
defineR r = throw (DefineRExc r)

--zeta

-- n0 == n1
swapOR :: Ring -> Ring
swapOR (OExp n0 k (Rot n1 d r)) | n0 == k * n1 && mod d k == 0 = (Rot n0 (div d k) (OExp n0 k r))
                                | otherwise = throw (SwapERExc (OExp n0 k (Rot n1 d r)))
swapOR r = throw (SwapERExc r)

swapIR :: Ring -> Ring
swapIR (IExp n0 k (Rot n1 d r)) | n0 == k * n1 && mod d k == 0 = (Rot n0 (div d k) (IExp n0 k r))
                                | otherwise = throw (SwapERExc (IExp n0 k (Rot n1 d r)))
swapIR r = throw (SwapERExc r)

_newDims :: (Int,Int,Int,Int) -> (Int,Int) 
_newDims (n0,k0,n1,k1) =
  let
    size_r = div n1 k1
    new_n0 = size_r*k0
    new_n1 = new_n0*k1 in
  (new_n0,new_n1)

swapOP :: Ring -> Ring
swapOP (OExp n0 k0 (Prod n1 k1 bnf)) =
  let
    (n0',n1') = _newDims (n0,k0,n1,k1)
    bnf2 = bnf :: BoundedNatFunc Ring
  in
    (Prod n1' k1 (BNF k1 (\i -> (OExp n0' k0 (bnf @ i)))))
swapOP r = throw (SwapEPExc r)

swapIP :: Ring -> Ring
swapIP (IExp n0 k0 (Prod n1 k1 bnf)) =
  let
    (n0',n1') = _newDims (n0,k0,n1,k1)
  in
    (Prod n1' k1 (BNF k1 (\i -> (IExp n0' k0 (bnf @ i)))))
swapIP r = throw (SwapEPExc r)

swapRP :: Ring -> Ring
swapRP (Rot n0 d (Prod n1 k bnf)) | n0 == n1 =
  (Prod n0 k (BNF k (\i ->  (Rot (div n0 k) d (bnf @ i)))))
                                  | otherwise = throw . SwapRPExc $ Rot n0 d (Prod n1 k bnf)
swapRP r = throw (SwapRPExc r)

_prod_double_index :: BoundedNatFunc Ring -> Int -> Int -> Ring
_prod_double_index bnf i j =
  let -- Maybe
    prod = bnf @ i
    (_,_,bnf2) = prod_get_data prod
  in
    bnf2 @ j

prod_get_data (Prod n k f) = (n,k,f)
prod_get_data r = throw (GE ("Excpected Product but got "++show r))

swapPP :: Ring -> Ring
swapPP (Prod n0 k0 bnf0) =
  let
    ring = bnf0 @ 0 
    (n1,k1,_) = prod_get_data ring
    (n0',n1') = _newDims (n0,k0,n1,k1)
  in
    Prod n1' k1 (BNF k1 (\j -> (Prod n0' k0 (BNF k0 (\i -> _prod_double_index bnf0 i j)))))

joinProd :: Ring -> Ring
joinProd (Prod n0 k0 bnf0) =
  let
    prod = bnf0 @ 0 
    (n1,k1,_) = prod_get_data prod
  in
    Prod n0 (k0*k1) (BNF (k0*k1) (\i -> _prod_double_index bnf0 (div i k1) (mod i k1)))

joinRot :: Ring -> Ring
joinRot (Rot n0 d0 (Rot n1 d1 r)) | n0 == n1 = Rot n0 (d0+d1) r
                                  | otherwise = error "joinRot: mismatched Rot dimensions"
                                  
data Morphism =
 MInverse Morphism |
 MReverse Morphism |
 FlippedCompose Morphism Morphism |
 ProdFunc Int Morphism |
 OExpFunc Int Morphism |
 IExpFunc Int Morphism |
 RotFunc Morphism |
 Factor Int |
 Stride Int |
 Clump Int |
 Norm |
 DefineI | DefineO | DefineR |
 SwapOR | SwapIR |
 SwapOP | SwapIP |
 SwapRP |
 JoinProd | SwapJoinProd |
 JoinRot |
 IdR
  deriving (Show,Eq,Ord)


pp_morph :: Morphism -> IO ()
pp_morph = putStrLn . pp_morph_h 0
  where
    pp_morph_h :: Int -> Morphism -> String
    pp_morph_h i (MInverse m) = _push_level i "Inv" m
    pp_morph_h i (MReverse m) = _push_level i "Rev" m
    pp_morph_h i (FlippedCompose m1 m2) = pp_morph_h i m1++pp_morph_h i m2
    pp_morph_h i (ProdFunc k m) = _push_level i ("ProdFunc "++show k) m
    pp_morph_h i (IExpFunc k m) = _push_level i ("IExpFunc "++show k) m
    pp_morph_h i (OExpFunc k m) = _push_level i ("OExpFunc "++show k) m
    pp_morph_h i (RotFunc m) =_push_level i ("RotFunc") m
    pp_morph_h i (Factor k) = (_indent i)++"Factor "++show k++"\n"
    pp_morph_h i (Stride k) = (_indent i)++"Stride "++show k++"\n"
    pp_morph_h i (Clump k) = (_indent i)++"Clump "++show k++"\n"
    pp_morph_h i Norm = (_indent i)++"Norm\n"
    pp_morph_h i DefineI = (_indent i)++"DefineI\n"
    pp_morph_h i DefineO = (_indent i)++"DefineO\n"
    pp_morph_h i DefineR = (_indent i)++"DefineR\n"
    pp_morph_h i SwapIR = (_indent i)++"SwapIR\n"
    pp_morph_h i SwapOR = (_indent i)++"SwapOR\n"
    pp_morph_h i SwapIP = (_indent i)++"SwapIP\n"
    pp_morph_h i SwapOP = (_indent i)++"SwapOP\n"
    pp_morph_h i SwapRP = (_indent i)++"SwapRP\n"
    pp_morph_h i JoinProd = (_indent i)++"JoinProd\n"
    pp_morph_h i SwapJoinProd = (_indent i)++"SwapJoinProd\n"
    pp_morph_h i JoinRot = (_indent i)++"JoinRot\n"
    pp_morph_h i IdR = (_indent i)++"IdR\n"

    _indent :: Int -> String
    _indent i | i /= 0 = " "++_indent (i-1)
              | otherwise = ""
    
    _push_level :: Int -> String -> Morphism -> String
    _push_level i name m =  (_indent i)++name++" (\n"++pp_morph_h (i+2) m++(_indent i)++")\n"
    
-- equivalent to type checking
apply :: Morphism -> Ring -> Ring
apply (Stride k) x = (stride k) x
apply (Clump k) x = (clump k) x
apply (Factor k) x = (factor k) x
apply (Norm) x = norm x
apply DefineO x = defineO x
apply DefineI x = defineI x
apply DefineR x = defineR x
apply SwapIR x = swapIR x
apply SwapOR x = swapOR x
apply SwapIP x = swapIP x
apply SwapOP x = swapOP x
apply SwapRP x = swapRP x
apply JoinProd x = joinProd x 
apply SwapJoinProd x =  joinProd . swapPP $ x
apply JoinRot x = joinRot x
apply (ProdFunc k0 m) (Prod n k bnf) | k0==k = Prod n k (BNF k (\i -> apply m (bnf @ i)))
                                 | otherwise = throw (GE "apply: ProdFunc: size values do not match")
apply (OExpFunc i m) (OExp n j x) | i==j = OExp n j (apply m x)
                                 | otherwise = throw (GE "apply: OExpFunc: size values do not match")
apply (IExpFunc i m) (IExp n j x) | i==j = IExp n j (apply m x)
                                 | otherwise = throw (GE "apply: IExpFunc: size values do not match")
apply (RotFunc m) (Rot n d x) = Rot n d (apply m x)
apply IdR x = x
apply (MInverse m) _ = throw (GE "apply: cannot apply inverse morphism") -- cannot apply Inverse Morphism
apply (MReverse m) r = apply m r
apply (FlippedCompose m1 m2) r = apply m2 . apply m1 $ r -- compose is backwards
apply m r = throw (GE ("morphism does not match ring structure: \n"++show m++"\n "++show r))


infixl 2 <.>
(<.>)=FlippedCompose

-- Pulls all composition out of functors (useful for mat translation)
-- Ignores MInverse
extract_compose :: Morphism -> [Morphism]
extract_compose m = ec_helper id m
  where
    -- collects functors on way down, replaces composition with append on way up
    ec_helper functor_map (ProdFunc k m) = ec_helper (functor_map . ProdFunc k) m
    ec_helper functor_map (OExpFunc k m) = ec_helper (functor_map . OExpFunc k) m
    ec_helper functor_map (IExpFunc k m) = ec_helper (functor_map . IExpFunc k) m
    ec_helper functor_map (RotFunc m)    = ec_helper (functor_map . RotFunc   ) m
    ec_helper functor_map (FlippedCompose m1 m2) =
      let
        ec_m1 = ec_helper functor_map m1
        ec_m2 = ec_helper functor_map m2
      in
        ec_m1 ++ ec_m2
    ec_helper functor_map m = [functor_map m]

morphism_map_down f (ProdFunc k m) = f (ProdFunc k (f m))
morphism_map_down f (OExpFunc k m) = f (OExpFunc k (f m))
morphism_map_down f (IExpFunc k m) = f (IExpFunc k (f m))
morphism_map_down f (RotFunc m)    = f (RotFunc    (f m))
morphism_map_down f (FlippedCompose m1 m2) = f (FlippedCompose (f m1) (f m2))

morphism_map_up f c (ProdFunc k m) = morphism_map_up f c m
morphism_map_up f c (OExpFunc k m) = morphism_map_up f c m
morphism_map_up f c (IExpFunc k m) = morphism_map_up f c m
morphism_map_up f c (RotFunc m)    = morphism_map_up f c m
morphism_map_up f c (FlippedCompose m1 m2) = c (morphism_map_up f c m1) (morphism_map_up f c m2)
morphism_map_up f _ m = f m

-- morph_simpl m = morphism_map_down ms_help m
--   where
--     ms_help (FlippedCompose m1 m2) =
--       if (morph_is_identity m1) then
--         m2
--       else
--         if (morph_is_identity m2) then
--           m1
--         else
--           (FlippedCompose m1 m2)
--     ms_help m = m   


morph_is_identity :: Morphism -> Bool
morph_is_identity m = morphism_map_up mii_help (&&) m
  where
    mii_help (Clump _) = True
    mii_help DefineI = True
    mii_help DefineR = True
    mii_help DefineO = True
    mii_help SwapIP = True
    mii_help SwapRP = True
    mii_help JoinProd = True
    mii_help JoinRot = True
    mii_help IdR = True
    mii_help m = False

slice :: Int -> Int -> [a] -> [a]
slice _ _ [] = []
slice l u (x:xs) | u < 0 = slice l (mod u (length xs + 1)) (x:xs)
                 | u==0 = []
                 | l==0 = x : (slice 0 (u-1) xs)
                 | otherwise = slice (l-1) (u-1) xs

apply_seq :: [Morphism] -> Ring -> Ring
apply_seq ms r = foldr apply r (reverse ms)

-----------------

-----------------


data Kernel
  = KInverse Kernel
  | KReverse Kernel
  | Phi Int Int Int Int Int -- n k d b p
  | Psi Int Int Int Int Int -- k m d b p
  | KL Int Int -- n k
  | KT Int Int Int -- di dj dk
  | KId Int -- n
  | Kernel_Extend Int Int (BoundedNatFunc Kernel) -- n k f
  | Kernel_OuterRepeat Int Int Kernel -- n k 
  | Kernel_InnerRepeat Int Int Kernel
  | Kernel_Compose Kernel Kernel
  deriving (Show,Eq)

kernel_dimension kernel = size . loc2lo (NR 1) . kernelToLOC $ kernel

morphism_to_kernel :: Ring -> Morphism -> Kernel
morphism_to_kernel r (MInverse m) = KInverse (morphism_to_kernel r m)
morphism_to_kernel r (MReverse m) = KReverse (morphism_to_kernel r m)
morphism_to_kernel r (FlippedCompose m1 m2) =
  let
    r2 = apply m1 r
  in
    Kernel_Compose (morphism_to_kernel r m1) (morphism_to_kernel r2 m2)
morphism_to_kernel (Prod n k0 bnf) (ProdFunc k1 m) | k0 == k1 = Kernel_Extend n k0 (BNF k0 (\i -> morphism_to_kernel (bnf @ i) m))
                                               | otherwise = throw (GE "m2k failed: prodfunc k value does not agree") -- should be caught by apply
morphism_to_kernel (OExp n k0 r) (OExpFunc k1 m) | k0 == k1 = Kernel_OuterRepeat n k0 (morphism_to_kernel r m) -- I_k0 \tensor ker
                                               | otherwise = throw (GE "m2k failed") -- should be caught by apply                                               
morphism_to_kernel (IExp n k0 r) (IExpFunc k1 m) | k0 == k1 = Kernel_InnerRepeat n k0 (morphism_to_kernel r m) -- ker \tensor I_k0
                                               | otherwise = throw (GE "m2k failed") -- should be caught by apply
morphism_to_kernel (Rot n d r) (RotFunc m) = morphism_to_kernel r m
morphism_to_kernel (Base n d b p) (Factor k) = Phi n k d b p
morphism_to_kernel (Base n d b p) (Stride k) = KL n (div n k)
morphism_to_kernel (Base n d b p) (Clump k) = KId n
morphism_to_kernel (Base n d b p) Norm = Psi n 1 d b p
morphism_to_kernel (IExp n k r) DefineI = KId n
morphism_to_kernel (OExp n k r) DefineO = KId n
morphism_to_kernel (Rot n d r) DefineR = KId n
morphism_to_kernel (OExp n0 k (Rot n1 d r)) SwapOR = Kernel_InnerRepeat n0 n1 (Psi k 1 d (get_root r) (get_prime r))
morphism_to_kernel (IExp n0 k (Rot n1 d r)) SwapIR = Kernel_OuterRepeat n0 n1 (Psi k 1 d (get_root r) (get_prime r))
morphism_to_kernel (OExp n0 k0 (Prod n1 k1 f)) SwapOP = KT k1 k0 (div n1 k1) -- could be expressed as tensor of L
morphism_to_kernel (IExp n0 k0 (Prod n1 k1 f)) SwapIP = KId n0 
morphism_to_kernel (Rot n0 d (Prod n1 k f)) SwapRP = KId n0
morphism_to_kernel (Prod n _ _) JoinProd = KId n
morphism_to_kernel (Prod n0 k0 bnf0) SwapJoinProd =
  let
    p = bnf0 @ 0
    (n1,k1,f1) = prod_get_data p
  in
    KT k1 k0 (div n1 k1)
morphism_to_kernel (Rot n0 d0 (Rot n1 d1 r)) JoinRot = KId n0
morphism_to_kernel r IdR = KId (get_dim r)

morphism_to_kernel_safe r m =
  let ker = morphism_to_kernel r m in
    if kernel_dimension ker /= get_dim r then
      error ("morphism_to_kernel: dimension mismatch "++show ker++" \n"++show r++"\n"++show m)
    else
      ker
      
morphism_seq_to_kernels :: Bool -> Ring -> [Morphism] -> [Kernel]
morphism_seq_to_kernels filter_id r (m:ms) =
  let
    next_r = apply m r
  in
    if filter_id && morph_is_identity m then
      morphism_seq_to_kernels filter_id next_r ms
    else
      (morphism_to_kernel_safe r m) : (morphism_seq_to_kernels filter_id next_r ms)
morphism_seq_to_kernels _ r [] = []

----

-- data FieldOps a = Const a | 
data LOClass
  = Diagonal Int (BoundedNatFunc FieldTimesROU)
  | LOCompose (LOClass) (LOClass)
  | Permutation Int (Int -> Int)
  | Square Int (BoundedNatFunc (BoundedNatFunc FieldTimesROU)) -- n 
  | ITensor Int Int (LOClass) -- (I_k \circledtimes LO_n) -- k n
  | TensorI Int Int (LOClass) -- (LO_n \circledtimes I_k) -- n k
  | Partition Int [LOClass] -- m (size of each partition)
  | LOId Int


kernelToLOC :: Kernel -> LOClass

kernelToLOC (Phi n k d b p) = 
  let
    square = Square k (BNF k (\x -> (BNF k (\y -> (phi_func_memo k k d b x y)))))
  in
  if n==k then
    square
  else
    TensorI n (div n k) square
-- kernelToLOC mpm (KInverse (Phi n k d b p)) =
--   let
--     square = (Square k (phi_inv_func_memo mpm k k d))
--   in
--   if n==k then
--     return square
--   else
--     return (ITensor n (div n k) square) 

kernelToLOC  (Psi k m d b p) =
  Diagonal (k*m) (BNF (k*m) (\x -> psi_func_memo k m d b x))

-- kernelToLOC mpm (KInverse (Psi k m d b p)) = return (Diagonal (k*m) (gamma_inv_func_memo mpm k m d))

kernelToLOC (KT di dj dk) = Permutation (di*dj*dk) (mT_perm di dj dk) -- applies inverse permutation (swaps di dj)
-- kernelToLOC _ (KInverse (KT di dj dk)) = return (Permutation (di*dj*dk) (mT_perm dj di dk)) -- applies inverse permutation (swaps di dj)

kernelToLOC (KL n k) = Permutation n (mL_perm n k)
-- kernelToLOC _ (KInverse (KL n k)) = return (Permutation n (mL_perm n (div n k)))

kernelToLOC  (KId n) = LOId n
-- kernelToLOC _ (KInverse (KId n)) = return (LOId n)

kernelToLOC  (Kernel_Extend n k bnf) =
  let kers = do -- List
        i<-[0..k-1]
        let ker = bnf @ i
        return (kernelToLOC  ker)
  in -- Maybe [LOCLass]
    Partition (div n k) kers
-- kernelToLOC mpm (KInverse (Kernel_Extend n k f)) =
--     let kers =
--           do -- List
--             i<-[0..k-1] :: [Int]
--             ker <- return (f i) :: [Kernel]
--             inv_ker <- kerneltoLOC mpm ( KInverse ker
--             return (do
--                        ker <- maybe_ker :: Maybe Kernel
--                        inv_ker <- return (KInverse ker) :: Maybe Kernel
--                        lo <- (kernelToLOC mpm) inv_ker :: Maybe LOClass
--                        return lo )) :: Maybe [LOClass]
--     in
--       kers >>= return . (Partition (div n k))

kernelToLOC  (Kernel_OuterRepeat n k ker) = ITensor k n (kernelToLOC ker)

kernelToLOC  (Kernel_InnerRepeat n k ker) = TensorI n k (kernelToLOC ker)
-- kernelToLOC mpm (KInverse (Kernel_Repeat n k ker)) =
--   let
--     inv_ker = KInverse ker
--     lops = sequence [kernelToLOC mpm inv_ker |i<-[0..k-1]]
--   in
--     lops >>= return . (Partition (div n k))

kernelToLOC (Kernel_Compose k1 k2) = LOCompose (kernelToLOC k1) (kernelToLOC k2)

-- -- pp_kernel :: Int -> Kernel -> String
-- -- pp_kernel i (KInverse m) = _push_level i "Inv" m
-- -- pp_kernel i (Kernel_Compose m1 m2) = pp_kernel i m1++pp_kernel i m2
-- -- pp_kernel i (Kernel_Extend n k f) = _push_level i ("Kernel_Extend "++show k) m
-- -- pp_kernel i (Kernel_Repeat k m) = _push_level i ("Kernel_Repeat "++show k) m
-- -- pp_kernel i (RotFunc m) =_push_level i ("RotFunc") m
-- -- pp_kernel i (Factor k) = (_indent i)++"Factor "++show k++"\n"
-- -- pp_kernel i (Label k) = (_indent i)++"Label "++show k++"\n"
-- -- pp_kernel i Norm = (_indent i)++"Norm\n"
-- -- pp_kernel i DefineE = (_indent i)++"DefineE\n"
-- -- pp_kernel i DefineR = (_indent i)++"DefineR\n"
-- -- pp_kernel i SwapER = (_indent i)++"SwapER\n"
-- -- pp_kernel i SwapEP = (_indent i)++"SwapEP\n"
-- -- pp_kernel i SwapRP = (_indent i)++"SwapRP\n"
-- -- pp_kernel i JoinProd = (_indent i)++"JoinProd\n"
-- -- pp_kernel i SwapJoinProd = (_indent i)++"SwapJoinProd\n"
-- -- pp_kernel i IdR = (_indent i)++"IdR\n"

nroot_mId :: NthRoots -> Int -> LinearOp FieldTimesROU
nroot_mId nr n = mId (fxr_zero nr) (fxr_one nr) n

loc2lo :: NthRoots -> LOClass -> LinearOp FieldTimesROU
loc2lo _ (LOCompose _ _) = error "LOCompose is not supported by loc2lo (must be flattened by extract_compose)"

loc2lo nr (Diagonal n bnf) =
  linearOp n (\(x,y) ->
                 if x==y then
                   bnf @ x
                 else
                   fxr_zero nr)

loc2lo _ (Square n bnf) =
  linearOp n (\(x,y) -> bnf @ x @ y)

loc2lo nr (Permutation n f) = linearOp n (\(x,y) -> if y == f x then (fxr_one nr) else (fxr_zero nr))

loc2lo nr (ITensor k n loc) =
  let
    lo = loc2lo nr loc
  in
    tensor fieldxrou_mult (nroot_mId nr k) lo

loc2lo nr (TensorI n k loc) =
  let
    lo = loc2lo nr loc
  in
    tensor fieldxrou_mult lo (nroot_mId nr k)

loc2lo (NR n) (Partition m locs) =
  let
    los = fmap (loc2lo (NR n)) locs
  in
    foldr (loParallel (FZero,RU n 1)) (nroot_mId (NR n) 0) los

loc2lo nr (LOId n) = nroot_mId nr n

-- -- data FieldOps a = Const a | 
-- data LOClass
--   = Diagonal Int (BoundedNatFunc FieldTimesROU)
--   | LOCompose (LOClass) (LOClass)
--   | Permutation Int (Int -> Int)
--   | Square Int (BoundedNatFunc (BoundedNatFunc FieldTimesROU)) -- n 
--   | ITensor Int Int (LOClass) -- (I_k \circledtimes LO_n) -- k n
--   | TensorI Int Int (LOClass) -- (LO_n \circledtimes I_k) -- n k
--   | Partition Int [LOClass] -- m (size of each partition)
--   | LOId Int

morphism_to_ker_seq :: Bool -> Ring -> Morphism -> [Kernel]
morphism_to_ker_seq filter_id r = morphism_seq_to_kernels filter_id r . extract_compose

morphism_to_lo_seq :: Ring -> Morphism -> [LinearOp FieldTimesROU]
morphism_to_lo_seq r = fmap (loc2lo (NR (get_root r)) . kernelToLOC) . morphism_seq_to_kernels True r . extract_compose

morph_get_states :: Ring -> Morphism -> [Ring]
morph_get_states ring morph =
  let
    ecm = extract_compose morph
  in
    scanl (\r m -> apply m r) ring ecm

display_morph :: Ring -> Morphism -> IO ()
display_morph r =
  putStr . foldr (\x y -> x++"\n"++y) "" . fmap show . morphism_to_lo_seq r

check_eq_morph :: ModPrimeMemo -> Ring -> Morphism -> Morphism -> LinearOp Bool
check_eq_morph mpm r m1 m2 | apply m1 r /= apply m2 r = error "morphisms are not syntactically equal on input ring"
                           | otherwise = lo_pointwise_op (==) lo1 lo2
  where
    lo1 = morphism_to_ff_lo mpm r m1
    lo2 = morphism_to_ff_lo mpm r m2
    
morphism_to_ff_lo :: ModPrimeMemo -> Ring -> Morphism -> LinearOp FField
morphism_to_ff_lo mpm r m = mult_lo_seq . fmap (fmap (get_ffield_emb (DPair mpm mpm)))  $ morphism_to_lo_seq r m

morphism_to_ff_lo_seq :: ModPrimeMemo -> Ring -> Morphism -> [LinearOp FField]
morphism_to_ff_lo_seq mpm r m = fmap (fmap (get_ffield_emb (DPair mpm mpm)))  $ morphism_to_lo_seq r m

pp_list :: Show a => [a] -> IO ()
pp_list l = putStrLn . foldr (\x y -> x++"\n\n"++y) "" . fmap show $ l

--- Testing

base l = Base (2^l) 0 (2^l) 1
mpm l = init_ModPrimeMemo 257 (2^l)

check_eq_by_subseq :: ModPrimeMemo -> Ring -> Morphism -> Morphism -> [((Int,Int),(Int,Int))] -> [LinearOp Bool]
check_eq_by_subseq mpm r m1 m2 sub_ind =
  let
    seq1 = morphism_to_ff_lo_seq mpm r m1
    seq2 = morphism_to_ff_lo_seq mpm r m2
  in
    do
      ((s1,e1),(s2,e2)) <- sub_ind
      let sub1 = split s1 e1 seq1
          sub2 = split s2 e2 seq2
          res1 = mult_lo_seq sub1
          res2 = mult_lo_seq sub2
      return $ lo_pointwise_op (==) res1 res2
      
     
    
internally_consist :: ModPrimeMemo -> Ring -> Morphism -> [Int] -> Bool
internally_consist mpm r m decomp =
  let
    seq1 = morphism_to_ff_lo_seq mpm r m
    pairs = reverse . snd . foldl (\(last,so_far) cur -> (cur,(last,cur):so_far)) (0,[]) $ decomp
    mult_and_reduce =  fmap (\x -> mod x (prime mpm)) . mult_lo_seq
    subseq = fmap (\(s,e) -> mult_lo_seq . split s e $ seq1) pairs
    
  in
    mult_lo_seq seq1 == mult_lo_seq subseq
