{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

import           Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range

import           Numeric.Peano

import           Control.Monad
import           Data.Ix

binaryProp
    :: forall a.
       Integral a
    => (forall t. Integral t => t -> t -> t)
    -> Integer
    -> Integer
    -> (Integer -> Integer -> Bool)
    -> Property
binaryProp op lb ub cond = property $ do
    x <- forAll (Gen.integral (Range.linear lb ub))
    y <- forAll (Gen.integral (Range.linear lb ub))
    guard (cond x y)
    let zb = op x y
    let zt = op (fromInteger @a x) (fromInteger y)
    zb === toInteger zt

holdsForLength :: Foldable f => (a -> Bool) -> f a -> Int
holdsForLength p = flip (foldr f id) 0 where
  f e a i | p e = a (i + 1)
          | otherwise = i

enumProps
    :: forall a.
       (Enum a, Show a, Ord a)
    => (Int -> Bool) -> Gen Int -> Gen a -> Property
enumProps p ig eg = property $ do
    x <- forAll ig
    annotate "from . to"
    (fromEnum . toEnum @a) x === x
    annotate "to . from"
    n <- forAll eg
    (toEnum . fromEnum) n === n
    annotate "[n..]"
    let lhs1 = take 100 $ map fromEnum [n..]
        rhs1 = take 100 [fromEnum n..]
        len1 = min (holdsForLength p lhs1) (holdsForLength p rhs1)
    take len1 lhs1 === take len1 rhs1
    annotate "[n,m..]"
    m <- forAll eg
    let lhs2 = take 100 $ map fromEnum [n,m..]
        rhs2 = take 100 [fromEnum n, fromEnum m..]
        len2 = min (holdsForLength p lhs2) (holdsForLength p rhs2)
    take len2 lhs2 === take len2 rhs2
    when (m >= n) $ do
        annotate "[n..m]"
        map fromEnum [n..m] === [fromEnum n..fromEnum m]
    l <- forAll eg
    when (((l > n) == (n > m)) && (l /= n)) $ do
        annotate "[l,n..m]"
        map fromEnum [l,n..m] === [fromEnum l, fromEnum n..fromEnum m]


prop_PeanoAdd :: Property
prop_PeanoAdd = binaryProp @Nat (+) 0 1000 (\_ _ -> True)

prop_PeanoMul :: Property
prop_PeanoMul = binaryProp @Nat (*) 0 1000 (\_ _ -> True)

prop_PeanoSub :: Property
prop_PeanoSub = withDiscards 1000 $ binaryProp @Nat (-) 0 1000 (>=)

prop_PeanoRem :: Property
prop_PeanoRem = binaryProp @Nat rem 0 1000 (\_ y -> y > 0)

prop_PeanoQuot :: Property
prop_PeanoQuot = binaryProp @Nat quot 0 1000 (\_ y -> y > 0)

-- prop_PeanoOrd :: Property
-- prop_PeanoOrd = property $ ord (Gen.integral (Range.linear @Nat 0 1000))(\n -> Gen.integral (Range.linear n (n+5)))

prop_PeanoEnum :: Property
prop_PeanoEnum =
    enumProps
        (>= 0)
        (Gen.integral (Range.linear 0 1000))
        (Gen.integral (Range.linear @Nat 0 1000))

prop_PeanoInRange :: Property
prop_PeanoInRange = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear 0 300))
    inRange (l,u) i === (l <= i &&  i <= u)

prop_PeanoIndex :: Property
prop_PeanoIndex = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear l u))
    unless (inRange (l,u) i) discard
    index (l,u) i === fromEnum (i - l)

main :: IO Bool
main = checkParallel $$(discover)
