{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

import           Hedgehog
import           Hedgehog.Main
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

nats :: Gen Nat
nats = Gen.integral (Range.linear 0 1000)

holdsForLength :: Foldable f => (a -> Bool) -> f a -> Int
holdsForLength p = flip (foldr f id) 0 where
  f e a i | p e = a (i + 1)
          | otherwise = i

prop_Enum :: Property
prop_Enum = property $ do
    x <- forAll (Gen.integral (Range.linear 0 1000))
    annotate "from . to"
    (fromEnum @Nat . toEnum) x === x
    annotate "to . from"
    n <- forAll nats
    (toEnum . fromEnum) n === n
    annotate "[n..]"
    let lhs1 = take 100 $ map fromEnum [n..]
        rhs1 = take 100 [fromEnum n..]
        len1 = min (holdsForLength (>= 0) lhs1) (holdsForLength (>= 0) rhs1)
    take len1 lhs1 === take len1 rhs1
    annotate "[n,m..]"
    m <- forAll nats
    let lhs2 = take 100 $ map fromEnum [n,m..]
        rhs2 = take 100 [fromEnum n, fromEnum m..]
        len2 = min (holdsForLength (>= 0) lhs2) (holdsForLength (>= 0) rhs2)
    take len2 lhs2 === take len2 rhs2
    when (m >= n) $ do
        annotate "[n..m]"
        map fromEnum [n..m] === [fromEnum n..fromEnum m]
    l <- forAll nats
    when (((l > n) == (n > m)) && (l /= n)) $ do
        annotate "[l,n..m]"
        map fromEnum [l,n..m] === [fromEnum l, fromEnum n..fromEnum m]

prop_Add :: Property
prop_Add = binaryProp @Nat (+) 0 1000 (\_ _ -> True)

prop_Mul :: Property
prop_Mul = binaryProp @Nat (*) 0 1000 (\_ _ -> True)

prop_Sub :: Property
prop_Sub = withDiscards 1000 $ binaryProp @Nat (-) 0 1000 (>=)

prop_Rem :: Property
prop_Rem = binaryProp @Nat rem 0 1000 (\_ y -> y > 0)

prop_quot :: Property
prop_quot = binaryProp @Nat quot 0 1000 (\_ y -> y > 0)

prop_ord :: Property
prop_ord = property $ do
  x <- forAll nats
  y <- forAll nats
  annotate "<="
  (x <= y) === (fromEnum x <= fromEnum y)
  (x <= x) === True
  annotate "<"
  (x < y) === (fromEnum x < fromEnum y)
  (x < x) === False
  annotate ">="
  (x >= y) === (y <= x)
  annotate ">"
  (x > y) === (y < x)
  annotate "compare"
  compare x y === compare (fromEnum x) (fromEnum y)

prop_InRange :: Property
prop_InRange = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear 0 300))
    inRange (l,u) i === (l <= i &&  i <= u)

prop_Index :: Property
prop_Index = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear l u))
    unless (inRange (l,u) i) discard
    index (l,u) i === fromEnum (i - l)

main :: IO ()
main = defaultMain [checkParallel $$(discover)]
