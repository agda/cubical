{-

This file contains:

- An implementation of the free groupoid (a free group that has no limitiations
  over the high dimensional path structure). An intermediate construction used
  to calculate the fundamental group of a Bouquet.

-}

module Cubical.HITs.FreeGroupoid.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data FreeGroupoid (A : Type ℓ) : Type ℓ where
  η     : A → FreeGroupoid A
  _·_     : FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
  ε     : FreeGroupoid A
  inv   : FreeGroupoid A → FreeGroupoid A
  assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
  idr   : ∀ x → x ≡ x · ε
  idl   : ∀ x → x ≡ ε · x
  invr  : ∀ x → x · (inv x) ≡ ε
  invl  : ∀ x → (inv x) · x ≡ ε
