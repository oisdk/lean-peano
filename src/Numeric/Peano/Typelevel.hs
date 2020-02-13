{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module Numeric.Peano.Typelevel where

import           GHC.TypeLits  (ErrorMessage (..), TypeError)
import qualified GHC.TypeLits  as Lit
import           Numeric.Peano

type family (==) (n :: Nat) (m :: Nat) :: Bool where
    Z == Z = True
    S n == S m = n == m
    Z == S _ = False
    S _ == Z = False

type family FromLit (n :: Lit.Nat) :: Nat where
    FromLit 0 = Z
    FromLit n = S (FromLit (n Lit.- 1))

type family ToLit (n :: Nat) :: Lit.Nat where
    FromLit Z = 0
    FromLit (S n) = 1 Lit.+ (ToLit n)

type family Compare (n :: Nat) (m :: Nat) :: Ordering where
    Compare Z Z         = EQ
    Compare (S n) (S m) = Compare n m
    Compare Z (S _)     = LT
    Compare (S _) Z     = GT

type family (<=) (n :: Nat) (m :: Nat) :: Bool where
    Z   <= _   = True
    S _ <= Z   = False
    S n <= S m = n <= m

type family (<) (n :: Nat) (m :: Nat) :: Bool where
    _ < Z = False
    n < S m = n <= m

type family Min (n :: Nat) (m :: Nat) :: Nat where
    Min Z _ = Z
    Min _ Z = Z
    Min (S n) (S m) = S (Min n m)

type family Max (n :: Nat) (m :: Nat) :: Nat where
    Max Z m = m
    Max n Z = n
    Max (S n) (S m) = S (Max n m)

infixl 6 +
type family (+) (n :: Nat) (m :: Nat) :: Nat where
    Z + m = m
    S n + m = S (n + m)

infixl 7 *
type family (*) (n :: Nat) (m :: Nat) :: Nat where
    Z   * _ = Z
    S n * m = m + n * m

infixl 6 -
type family (-) (n :: Nat) (m :: Nat) :: Nat where
    n   - Z   = n
    S n - S m = n - m
    Z   - S _ = Z

type family (%) (n :: Nat) (m :: Nat) :: Nat where
    _ % Z = TypeError (Text "divide by zero")
    n % m = Rem' n m n m

type family Rem' (n :: Nat) (m :: Nat) (n' :: Nat) (m' :: Nat) :: Nat where
    Rem' n m n' Z = Rem' n' m n' m
    Rem' n m (S n') (S m') = Rem' n m n' m'
    Rem' n m Z (S _) = n

type family (/) (n :: Nat) (m :: Nat) :: Nat where
    _ / Z = TypeError (Text "divide by zero")
    n / m = Div' m n m

type family Div' (m :: Nat) (n' :: Nat) (m' :: Nat) :: Nat where
    Div' m n' Z = S (Div' m n' m)
    Div' m (S n') (S m') = Div' m n' m'
    Div' m Z (S _) = Z
