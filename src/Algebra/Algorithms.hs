module Algebra.Algorithms where

import Algebra.PolyRings


-- seiler_register_tiles :: Morphism
-- seiler_register_tiles n k inner =
--     (Clump
--     (Stride k) <.>
--     (OExpFunc k (inner (divnk))) <.>
--     SwapOP <.>
--     ProdFunc divnk (
--       DefineO <.>
--       inner k) <.>
--     JoinProd

in_place :: Morphism
in_place =
  Norm <.>
  RotFunc (Factor 2) <.>
  SwapRP <.>
  ProdFunc 2 DefineR

seiler_1 :: Int -> Morphism
seiler_1 2 =  Factor 2
seiler_1 n =
    Factor 2 <.>
    ProdFunc 2 (seiler_1 (div n 2)) <.>
    JoinProd
      
seiler_2 :: Int -> Morphism
seiler_2 2 = in_place
seiler_2 n =
  Clump (div n 2) <.>
  IExpFunc (div n 2) in_place <.>
  SwapIP <.>
  ProdFunc 2 (
    DefineI <.>
    seiler_2 (div n 2)) <.>
  JoinProd

seiler_register_tiles :: Int -> Morphism
seiler_register_tiles n =
  let no4 = div n 4 in
  Clump no4 <.>
  IExpFunc no4 (
    Stride 2 <.>
    OExpFunc 2 (in_place) <.>
    SwapOP) <.>
  SwapIP <.>
  ProdFunc 2 (
    IExpFunc no4 (
      DefineO <.>
      in_place) <.>
    SwapIP <.>
    ProdFunc 2 (
      DefineI <.>
      seiler_2 no4) <.>
    JoinProd) <.>
  JoinProd

-- seiler_register_tiles :: Morphism
-- seiler_register_tiles = register_tiles 256 4 seiler_2

------------------------------

spiral_4_step :: Int -> Int -> Morphism
spiral_4_step n k =
  let m = div n k in
    Factor k <.>
    ProdFunc k (
      Norm <.>
      RotFunc (Factor m) <.>
      SwapRP <.>
      ProdFunc m DefineR) <.>
    SwapJoinProd

-----------------
-- coppersmith QFT

-- Base(2^k,d) -> I(2)^(k-1) B(2,d)
qubitify :: Int -> Morphism
qubitify l | l<=1 = IdR
             | l==2 = Clump 2
             | otherwise = Clump 2 <.>
                           IExpFunc 2 (qubitify (l-1))

-- unwraps l many IExpFunc
qubitFunctor :: Int -> (Morphism -> Morphism)
qubitFunctor l m
  | l < 0 = error "qubitFunctor called with l < 0"
  | l==0 = m 
  | otherwise = IExpFunc 2 (qubitFunctor (l-1) m)

qqft l = qubitify l <.> qft l
-- assumes input is of form I(2)^(l-1) B(2,0) (qubitified) (for l>1)
-- produces output of form P(2) R(i*N/2^(l-1)) I(2)^(l-2) B(2,0) 
qft :: Int -> Morphism
qft l | l==1 = Factor 2
      | otherwise =
        qubitFunctor (l-2) (
          IExpFunc 2 (Factor 2) <.>
          SwapIP <.>
          ProdFunc 2 (
              DefineI <.>
              Norm )) <.>
        (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIP | i<-[3..l]]) <.>
        ProdFunc 2 (
          (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIR | i<-[3..l]] ) <.>
          RotFunc (qft (l-1)) <.>
          SwapRP <.>
          ProdFunc (2^(l-1)) DefineR ) <.>
        JoinProd

--- B(2^l,0) -> P(2) R B(2^(l-1),0)
qft_grouped :: Int -> Morphism
qft_grouped l | l == 1 = Factor 2
              | otherwise =
                Clump (2^(l-1)) <.> -- I_(2^(l-2)) B_2
                IExpFunc (2^(l-1)) (
                  -- Clump 2 <.> -- I_(2^(l-2)) I_2 B_2
                  (Factor 2)) <.> -- I_(2^(l-1)) P_2 B_1
                  -- SwapIP) <.> -- I_(2^(l-2)) P_2 I_2 B_1
                SwapIP <.> -- P_2 I_(2^(l-1)) B_1
                ProdFunc 2 (
                  DefineI <.> -- P_2 I_(2^(l-2)) B_2
                  -- DefineI <.> -- P_2 B_(2^(l-1))
                  Norm <.> -- P_2 R B_(2^(l-1))
                  -- Clump (2^(l-2)) <.> -- P_2 R I_(2^(l-2)) B_2
                  RotFunc (qft_grouped (l-1)) <.> -- P_2 R P_(2^(l-1)) B_1
                  SwapRP <.> -- P_2 P_(2^(l-1)) R B_1
                  ProdFunc (2^(l-1)) DefineR) <.> -- P_2 P_(2^(l-1)) B_1
                JoinProd -- P_(2^l) B_1
                
                  
--qft_cleanup l | l==1 
        
-- Doesn't work: normalizing bases with different rotations is not 1 gate operation (DefineR cannot be used)
-- assumes input is of form I(2)^(l-1) B(2,0) (qubitified)
-- produces output of form P(2) I(2)^(l-2) R B(2,0) 
qft_better :: Int -> Morphism
qft_better l = qft_better_head l qft_better_tail

-- I(2)^(l-1) B(2,0) -> P(2) I(2)^(l-2) R B(2,0)
qft_better_head l tail | l==1 = Factor 2
                       | otherwise =
   qubitFunctor (l-2) (
     IExpFunc 2 (Factor 2) <.>
     SwapIP <.>
     ProdFunc 2 (
       DefineI <.>
       Norm )) <.>
     (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIP | i<-[3..l]]) <.>
     ProdFunc 2 (tail (l-1))
        
-- I(2)^(l-1) R B(2,0) -> P(2) I(2)^(l-2) R B(2,0)
qft_better_tail l | l==1 = RotFunc (Factor 2) <.> SwapRP
                      | otherwise = 
      qubitFunctor (l-2) (
        IExpFunc 2 ( -- (IExp 2)*(l-2)( IExp 2 (Rot (Base 2)))
          RotFunc (Factor 2) <.> -- (IExp 2)*(l-2)( IExp 2 (Rot (Prod 2 (Base 1))))
          SwapRP <.> -- (IExp 2)*(l-2)( IExp 2 (Prod 2 (Rot (Base 1))))
          ProdFunc 2 DefineR) <.>  -- (IExp 2)*(l-2)( IExp 2 (Prod 2 (Base 1)))
        SwapIP <.>  -- (IExp 2)*(l-2)( Prod 2 (IExp 2 (Base 1)))
        ProdFunc 2 (
          -- SwapIR <.> -- (IExp 2)*(l-2)( Prod 2 (IExp 2 (Base 1)))
          DefineI <.> -- (IExp 2)*(l-2)( Prod 2 (Base 2))
          Norm)) <.>  -- (IExp 2)*(l-2)( Prod 2 (Rot (Base 2)))
      (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIP | i<-[3..l]]) <.>
        -- Prod 2 ((IExp 2)*(l-2)( Rot (Base 2)))
      ProdFunc 2 (qft_better_tail (l-1))

qqft_better_2 l = qubitify l <.> qft_better_2 l

-- I(2)^(l-1) R B(2,0) -> P(2) I(2)^(l-2) R B(2,0)
qft_better_2 :: Int -> Morphism
qft_better_2 l = qft_better_head l qft_better_2_tail
  where
    qft_better_2_head l | l==1 = Factor 2
                        | otherwise =
      qubitFunctor (l-2) (
        IExpFunc 2 (Factor 2) <.>
        SwapIP <.>
        ProdFunc 2 (
          DefineI <.>
          Norm )) <.>
        (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIP | i<-[3..l]]) <.>
        ProdFunc 2 (qft_better_2_tail (l-1))

    -- I(2)^(l-1) B(2,0) -> P(2) I(2)^(l-2) R B(2,0)
    qft_better_2_tail l | l==1 = RotFunc (Factor 2) <.> SwapRP
                        | otherwise =
      qubitFunctor (l-2) (
        IExpFunc 2 (
          RotFunc (Factor 2) <.>
          SwapRP ) <.>
        SwapIP <.> -- (IExp 2)*(l-2)( Prod 2 (IExp 2 (Rot (Base 1))))
        ProdFunc 2 (
          SwapIR <.> -- (IExp 2)*(l-2)( Prod 2 (Rot (IExp 2 (Base 1))))
          RotFunc (
            DefineI <.> -- (IExp 2)*(l-2)( Prod 2 (Rot (Base 2)))
            Norm) <.>  -- (IExp 2)*(l-2)( Prod 2 (Rot (Rot (Base 2))))
          JoinRot)) <.> -- (IExp 2)*(l-2)( Prod 2 (Rot (Base 2)))
      (foldr (<.>)  IdR [qubitFunctor (l-i) SwapIP | i<-[3..l]]) <.>
      ProdFunc 2 (qft_better_2_tail (l-1))
        
qft8 :: Morphism
qft8 =
  Clump 2 <.> -- IExp 2 (Base 4)
  IExpFunc 2 (
    Clump 2 <.>  -- IExp 2 (IExp 2 (Base 2))
    IExpFunc 2 (
      Factor 2) <.> -- IExp 2 (IExp 2 (Prod 2 (Base 1)))
    SwapIP <.>  -- IExp 2 (Prod 2 (IExp 2 (Base 1)))
    ProdFunc 2 (
      DefineI <.> -- IExp 2 (Prod 2 (Base 2))
      Norm )) <.>  -- IExp 2 (Prod 2 (Rot (Base 2)))
  SwapIP <.> -- Prod 2 (IExp 2 (Rot (Base 2)))
  ProdFunc 2 (
    SwapIR <.> -- Prod 2 (Rot (IExp 2 (Base 2)))
    RotFunc (
      IExpFunc 2 (Factor 2) <.>  -- Prod 2 (Rot (IExp 2 (Prod 2 (Base 1))))
      SwapIP <.> -- Prod 2 (Rot (Prod 2 (IExp 2 (Base 1))))
      ProdFunc 2 (
        DefineI <.> -- Prod 2 (Rot (Prod 2 (Base 2)))
        Norm) <.>  -- Prod 2 (Rot (Prod 2 (Rot (Base 2))))
      ProdFunc 2 (RotFunc (Factor 2)))) -- Prod 2 (Rot (Prod 2 (Rot (Prod 2 (Base 1)))))
      
               
bitreversal :: Int -> Morphism
bitreversal l | l==1 = Factor 2
              | otherwise =
                Factor 2 <.>
                ProdFunc 2 (bitreversal (l-1)) <.>
                JoinProd


swapIR_test16 :: Morphism
swapIR_test16 =
  Clump 4 <.>
  IExpFunc 4 ( -- I4 B4
    Clump 2 <.> -- I4 I2 B2
    IExpFunc 2 (Factor 2) <.> -- I4 I2 P2 B1
    SwapIP <.> -- I4 P2 I2 B1
    ProdFunc 2 (
      DefineI <.> -- I4 P2 B2
      Norm <.>  -- I4 P2 R B2
      RotFunc (Factor 2))) <.> -- I4 P2 R P2 B1
  SwapIP <.> -- P2 I4 R P2 B1
  ProdFunc 2 (
    SwapIR <.> -- P2 R I4 P2 B1
    RotFunc (
      SwapIP <.> -- P2 R P2 I4 B1
      ProdFunc 2 (
          DefineI <.> -- P2 R P2 B4
          Factor 4)) <.> -- P2 R P2 P4 B1
    SwapRP <.> -- P2 P2 R P4 B1
    ProdFunc 2 (
      SwapRP <.> -- P2 P2 P4 R B1
      ProdFunc 4 DefineR) <.> -- P2 P2 P4 B1
    SwapJoinProd) <.> -- P2 P8 B1
  SwapJoinProd -- P16 B1
    
    


