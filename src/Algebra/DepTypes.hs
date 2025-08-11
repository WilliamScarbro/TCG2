{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Algebra.DepTypes where

class (Show a,Show b) => DepType a b where
  is_instance :: a -> b -> Bool

depTypeChecked :: (DepType a b,Show a,Show b) => a -> b -> b
depTypeChecked a b = if is_instance a b then b else error ("Dep Type Check fail: "++show b++" is not an instance of "++show a)

data DEither a b = DEither a b deriving Show

instance (DepType a b, DepType c d) => DepType (DEither a c) (Either b d) where
  is_instance (DEither a c) (Left b) = is_instance a b
  is_instance (DEither a c) (Right d) = is_instance c d

data DPair a b = DPair a b deriving Show

instance (DepType a b, DepType c d) => DepType (DPair a c) (b,d) where
  is_instance (DPair a c) (b,d) = is_instance a b && is_instance c d
  
  

class DepType a b => Has01 a b where
  get_zero :: a -> b
  get_one :: a -> b

-- get_zero :: DepType a b => a -> b 
-- get_zero a b = _get_zero a (depTypeChecked a b)

-- get_one :: DepType a b => a -> b
-- get_one a b = _get_one a (depTypeChecked a b)

class DepType context a => HasIntEmb context a where
  _get_int_emb :: context -> a -> Int

get_int_emb :: HasIntEmb context a => context -> a -> Int
get_int_emb context a = _get_int_emb context (depTypeChecked context a)


data Zero = Zero deriving (Show,Eq,Ord)
