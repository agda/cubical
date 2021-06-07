{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.RawRing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.RingSolver.AlmostRing hiding (⟨_⟩)

private
  variable
    ℓ : Level

record RawRing ℓ : Type (ℓ-suc ℓ) where

  constructor rawring

  field
    Carrier : Type ℓ
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ : RawRing ℓ → Type ℓ
⟨_⟩ = RawRing.Carrier

AlmostRing→RawRing : AlmostRing ℓ → RawRing ℓ
AlmostRing→RawRing (almostring Carrier 0r 1r _+_ _·_ -_ isAlmostRing) =
                   rawring Carrier 0r 1r _+_ _·_ -_
