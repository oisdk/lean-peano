{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Peano numerals. Effort is made to make them as efficient as
-- possible, and as lazy as possible, but they are many orders of
-- magnitude less efficient than machine integers. They are primarily
-- used for type-level programming, and occasionally for calculations
-- which can be short-circuited.
--
-- For instance, to check if two lists are the same length, you could
-- write:
--
-- @
-- 'length' xs == 'length' ys
-- @
--
-- But this unnecessarily traverses both lists. The more efficient
-- version, on the other hand, is less clear:
--
-- @
-- sameLength [] [] = True
-- sameLength (_:xs) (_:ys) = sameLength xs ys
-- sameLength _ _ = False
-- @
--
-- Using @'Data.List.genericLength'@, on the other hand, the laziness of
-- @'Nat'@ will indeed short-circuit:
--
-- >>> genericLength [1,2,3] == genericLength [1..]
-- False
module Numeric.Peano where

import           Data.List       (unfoldr)

import           Control.DeepSeq (NFData (rnf))

import           Data.Data       (Data, Typeable)
import           GHC.Generics    (Generic)

import           Numeric.Natural

import           Data.Ix

import           Data.Function
import           Text.Read

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (genericLength)
-- >>> default (Nat)
-- >>> :{
-- instance Arbitrary Nat where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Peano numbers. Care is taken to make operations as lazy as
-- possible:
--
-- >>> 1 > S (S undefined)
-- False
-- >>> Z > undefined
-- False
-- >>> 3 + undefined >= 3
-- True
data Nat
    = Z
    | S Nat
    deriving (Eq,Generic,Data,Typeable)

-- | A right fold over the naturals.
-- Alternatively, a function which converts a natural into
-- a Church natural.
--
-- prop> foldrNat S Z n === n
foldrNat :: (a -> a) -> a -> Nat -> a
foldrNat f k = go
  where
    go Z     = k
    go (S n) = f (go n)
{-# INLINE foldrNat #-}

-- | A strict left fold over the naturals.
foldlNat' :: (a -> a) -> a -> Nat -> a
foldlNat' f = go
  where
    go !b Z     = b
    go !b (S n) = go (f b) n
{-# INLINE foldlNat' #-}

-- | As lazy as possible
instance Ord Nat where
    compare Z Z         = EQ
    compare (S n) (S m) = compare n m
    compare Z (S _)     = LT
    compare (S _) Z     = GT

    Z   <= _ = True
    S n <= m = n < m

    _ < Z   = False
    n < S m = n <= m

    (>=) = flip (<=)
    (>)  = flip (<)

    min Z _         = Z
    min _ Z         = Z
    min (S n) (S m) = S (min n m)

    max Z     m = m
    max (S n) m = S (case m of
      Z    -> n
      S pm -> max n pm)

-- | Subtraction stops at zero.
--
-- prop> n >= m ==> m - n == Z
instance Num Nat where
    n + m = foldrNat S m n
    n * m = foldrNat (m+) Z n
    abs = id
    signum Z     = Z
    signum (S _) = S Z
    fromInteger n
        | n < 0 = error "cannot convert negative integers to Peano numbers"
        | otherwise = go n where
            go 0 = Z
            go m = S (go (m-1))
    S n - S m = n - m
    n   - _   = n

-- | The maximum bound here is infinity.
--
-- prop> maxBound > (n :: Nat)
instance Bounded Nat where
    minBound = Z
    maxBound = fix S

-- | Shows integer representation.
instance Show Nat where
    showsPrec n = showsPrec n . toInteger

-- | Reads the integer representation.
instance Read Nat where
    readPrec = fmap (fromIntegral :: Natural -> Nat) readPrec

-- | Will obviously diverge for values like `maxBound`.
instance NFData Nat where
    rnf Z     = ()
    rnf (S n) = rnf n

instance Real Nat where
    toRational = toRational . toInteger

-- | Uses custom 'enumFrom', 'enumFromThen', 'enumFromThenTo' to avoid
-- expensive conversions to and from 'Int'.
--
-- >>> [1..3]
-- [1,2,3]
-- >>> [1..1]
-- [1]
-- >>> [2..1]
-- []
-- >>> take 3 [1,2..]
-- [1,2,3]
-- >>> take 3 [5,4..]
-- [5,4,3]
-- >>> [1,3..7]
-- [1,3,5,7]
-- >>> [5,4..1]
-- [5,4,3,2,1]
-- >>> [5,3..1]
-- [5,3,1]
instance Enum Nat where
    succ = S
    pred (S n) = n
    pred Z     = error "pred called on zero nat"
    fromEnum = foldlNat' succ 0
    toEnum m
      | m < 0 = error "cannot convert negative number to Peano"
      | otherwise = go m
      where
        go 0 = Z
        go n = S (go (n - 1))
        
    enumFrom = iterate S
    
    enumFromTo n m = unfoldr f (n, S m - n)
      where
        f (_,Z)   = Nothing
        f (e,S l) = Just (e, (S e, l))

    enumFromThen n m = n : unfoldr (ts n m) n
      where
        ts Z m         = add m
        ts n Z         = sub n
        ts (S n) (S m) = ts n m

        add m n = let r = m + n in Just (r, r)

        sub Z     n     = Just (n,n)
        sub (S _) Z     = Nothing
        sub (S m) (S n) = sub m n

    enumFromThenTo n m t = ts n m
      where
        n' = fromEnum n
        t' = fromEnum t

        ts (S nn) (S mm) = ts nn mm
        ts Z mm          = unfoldr (up (fromEnum mm)) ((t' + 1) - n', n)
        ts nn Z          = unfoldr (down (fromEnum nn)) ((n' + 1) - t', n)

        up m (t, n)
          | t <= 0 = Nothing
          | otherwise = Just (n, (t - m, add m n))
          
        down m (t, n)
          | t <= 0 = Nothing
          | otherwise = Just (n, (t - m, sub m n))
    
        add 0 x = x
        add n x = S (add (n-1) x)
        
        sub 0 x = x
        sub n (S x) = sub (n-1) x
        sub _ Z = Z

-- | Errors on zero.
--
-- >>> 5 `div` 2
-- 2
instance Integral Nat where
    toInteger = foldlNat' succ 0
    quotRem _ Z = (maxBound, error "divide by zero")
    quotRem n' (S m) = go Z n' m
      where
        go k Z     _     = (Z, k)
        go _ (S n) Z     = fsuc (go Z n m)
        go k (S n) (S j) = go (S k) n j

        fsuc ~(x, y) = (S x, y)

    quot _ Z = maxBound
    quot n' (S m) = go n' m
      where
        go Z _         = Z
        go (S n) Z     = S (go n m)
        go (S n) (S j) = go n j

    rem _ Z = error "divide by zero"
    rem n' (S m) = go Z n' m
      where
        go k Z _ = k
        go _ (S n) Z = go Z n m
        go k (S n) (S j) = go (S k) n j

    div = quot
    mod = rem
    divMod = quotRem

instance Ix Nat where
    range = uncurry enumFromTo
    inRange = uncurry go where
      go (S _) _ Z         = False
      go Z y x             = x <= y
      go (S x) (S y) (S z) = go x y z
      go (S _) Z (S _)     = False
    index = uncurry go where
      go Z h i             = lim 0 h i
      go (S _) _ Z         = error "out of range"
      go (S l) (S h) (S i) = go l h i
      go (S _) Z (S _)     = error "out of range"
      lim _ Z (S _)      = error "out of range"
      lim !a (S n) (S m) = lim (a + 1) n m
      lim !a _ Z         = a
