{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

-- | Simple type-level Peano naturals.
module Numeric.Peano.Typelevel
  ( type (==)
  , type FromLit
  , type ToLit
  , type Compare
  , type (<=)
  , type (<)
  , type Min
  , type Max
  , type (+)
  , type (*)
  , type (-)
  , type (%)
  , type (/)
  ) where

import           GHC.TypeLits  (ErrorMessage (..), TypeError)
import qualified GHC.TypeNats  as Lit
import           Numeric.Peano

-- | Equality of type-level naturals.
type family (==) (n :: Nat) (m :: Nat) :: Bool where
    Z == Z = True
    S n == S m = n == m
    Z == S _ = False
    S _ == Z = False

-- | Conversion of numeric literals to naturals.
type family FromLit (n :: Lit.Nat) :: Nat where
    FromLit 0 = Z
    FromLit n = S (FromLit (n Lit.- 1))

-- | Conversion of naturals to numeric literals.
type family ToLit (n :: Nat) :: Lit.Nat where
    ToLit Z = 0
    ToLit (S n) = 1 Lit.+ (ToLit n)

-- | Comparison of type-level naturals.
type family Compare (n :: Nat) (m :: Nat) :: Ordering where
    Compare Z Z         = EQ
    Compare (S n) (S m) = Compare n m
    Compare Z (S _)     = LT
    Compare (S _) Z     = GT

-- | '<=' on type-level naturals.
type family (<=) (n :: Nat) (m :: Nat) :: Bool where
    Z   <= _ = True
    S n <= m = n < m

-- | '<' on type-level naturals.
type family (<) (n :: Nat) (m :: Nat) :: Bool where
    _ < Z   = False
    n < S m = n <= m

-- | The minimum of two type-level naturals.
type family Min (n :: Nat) (m :: Nat) :: Nat where
    Min Z _ = Z
    Min _ Z = Z
    Min (S n) (S m) = S (Min n m)

-- | The maximum of two type-level naturals.
type family Max (n :: Nat) (m :: Nat) :: Nat where
    Max Z m = m
    Max n Z = n
    Max (S n) (S m) = S (Max n m)

-- | Addition of type-level naturals.
infixl 6 +
type family (+) (n :: Nat) (m :: Nat) :: Nat where
    Z + m = m
    S n + m = S (n + m)

-- | Multiplication of type-level naturals.
infixl 7 *
type family (*) (n :: Nat) (m :: Nat) :: Nat where
    Z   * _ = Z
    S n * m = m + n * m

-- | Subtraction of type-level naturals.
infixl 6 -
type family (-) (n :: Nat) (m :: Nat) :: Nat where
    Z   - _   = Z
    n   - Z   = n
    S n - S m = n - m

-- | Remainder on type-level naturals.
type family (%) (n :: Nat) (m :: Nat) :: Nat where
    _ % Z = TypeError (Text "divide by zero")
    n % m = Rem' n m n m

type family Rem' (n :: Nat) (m :: Nat) (n' :: Nat) (m' :: Nat) :: Nat where
    Rem' n m n' Z = Rem' n' m n' m
    Rem' n m (S n') (S m') = Rem' n m n' m'
    Rem' n m Z (S _) = n

-- | Division on type-level naturals.
type family (/) (n :: Nat) (m :: Nat) :: Nat where
    _ / Z = TypeError (Text "divide by zero")
    n / m = Div' m n m

type family Div' (m :: Nat) (n' :: Nat) (m' :: Nat) :: Nat where
    Div' m n' Z = S (Div' m n' m)
    Div' m (S n') (S m') = Div' m n' m'
    Div' m Z (S _) = Z
