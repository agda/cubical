{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}

module Cubical.HITs.FreeGroup.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data FreeGroup (A : Type ℓ) : Type ℓ where
  η     : A → FreeGroup A
  _·_   : FreeGroup A → FreeGroup A → FreeGroup A
  ε     : FreeGroup A
  inv   : FreeGroup A → FreeGroup A
  assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
  idr   : ∀ x → x ≡ x · ε
  idl   : ∀ x → x ≡ ε · x
  invr  : ∀ x → x · (inv x) ≡ ε
  invl  : ∀ x → (inv x) · x ≡ ε
  trunc : isSet (FreeGroup A)
