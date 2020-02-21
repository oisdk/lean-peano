{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveGeneric        #-}

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

import           Data.List                   (unfoldr)

import           Control.DeepSeq             (NFData (rnf))

import           Data.Data                   (Data, Typeable)
import           GHC.Generics                (Generic)

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
    go !b Z = b
    go !b (S n) = go (f b) n
{-# INLINE foldlNat' #-}

-- | As lazy as possible
instance Ord Nat where
    compare Z Z         = EQ
    compare (S n) (S m) = compare n m
    compare Z (S _)     = LT
    compare (S _) Z     = GT

    Z   <= _   = True
    S _ <= Z   = False
    S n <= S m = n <= m

    _ < Z = False
    n < S m = n <= m

    (>=) = flip (<=)
    (>) = flip (<)

    min Z _ = Z
    min _ Z = Z
    min (S n) (S m) = S (min n m)

    max Z m = m
    max n Z = n
    max (S n) (S m) = S (max n m)

-- | Subtraction stops at zero.
--
-- prop> n >= m ==> m - n == Z
instance Num Nat where
    n + m = foldrNat S m n
    n * m = foldrNat (m+) Z n
    abs = id
    signum Z = Z
    signum (S _) = S Z
    fromInteger n
        | n < 0 = error "cannot convert negative integers to Peano numbers"
        | otherwise = go n where
            go 0 = Z
            go m = S (go (m-1))
    n   - Z   = n
    S n - S m = n - m
    Z   - S _ = Z

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
    pred Z = error "pred called on zero nat"
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
        f (_,Z) = Nothing
        f (e,S l) = Just (e, (S e, l))
    enumFromThen n m = iterate t n
      where
        ts Z mm = (+) mm
        ts (S nn) (S mm) = ts nn mm
        ts nn Z = subtract nn
        t = ts n m
    enumFromThenTo n m t = unfoldr f (n, jm)
      where
        ts (S nn) (S mm) = ts nn mm
        ts Z mm = (S t - n, (+) mm, mm)
        ts nn Z = (S n - t, subtract nn, nn)
        (jm,tf,tt) = ts n m
        td = subtract tt
        f (_,Z) = Nothing
        f (e,l@(S _)) = Just (e, (tf e, td l))


-- | Errors on zero.
--
-- >>> 5 `div` 2
-- 2
instance Integral Nat where
    toInteger = foldlNat' succ 0
    quotRem _ Z = (maxBound, error "divide by zero")
    quotRem x y = qr Z x y
      where
        qr q n m = go n m
          where
            go nn Z          = qr (S q) nn m
            go (S nn) (S mm) = go nn mm
            go Z (S _)       = (q, n)
    quot n m = go n where
      go = subt m where
        subt Z nn          = S (go nn)
        subt (S mm) (S nn) = subt mm nn
        subt (S _) Z       = Z
    rem _ Z = error "divide by zero"
    rem nn mm = r nn mm where
      r n m = go n m where
        go nnn Z           = r nnn m
        go (S nnn) (S mmm) = go nnn mmm
        go Z (S _)         = n
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
