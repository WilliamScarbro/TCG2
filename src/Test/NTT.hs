module Main where

import Test.Hspec
import Algebra.NTT
import Algebra.Util

ntt_spec :: Spec
ntt_spec =
  describe "NTT tests" $ do
    it "test mult_lo_seq" $ do
      let lo1 = linearOp 2 (\(i,j) -> 2*i+j)
          lo2 = linearOp 2 (\(i,j) -> 3*i+2*j-4)
          lo3 = linearOp 2 (\(i,j) -> 3*j+i-2)
      mm (mm lo1 lo2) lo3 `shouldBe` mult_lo_seq [lo1,lo2,lo3]
    it "test mult_lo_seq assoc 4" $ do
      let seq = [linearOp 8 (\(i,j) -> x*i+j) | x<-[2..10]]
          mar = fmap (\x -> mod x 257) . mult_lo_seq
      mar [mar $ split 0 1 seq, mar $ split 1 9 seq] `shouldBe` mar seq
    -- it "my_mm is same as mm" $ do
    --   let seq = [linearOp 8 (\(i,j) -> x*i+j) | x<-[2..10]]
    --       mm_res = foldl mm (head seq) (tail seq)
    --       my_mm_res = foldl my_mm (head seq) (tail seq)
    --   mm_res `shouldBe` my_mm_res

    it "test reduction" $ do
      let seq =  [linearOp 8 (\(i,j) -> x*i+j) | x<-[3..10]]
          mar = fmap (\x -> mod x 257) . mult_lo_seq
          LO m = mult_lo_seq seq
      mar seq `shouldBe` LO m -- (LO (fmap (\x -> mod x 257) m)) 
main = hspec ntt_spec
