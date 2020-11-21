{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RawAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.RingSolver.AlmostRing hiding (⟨_⟩)
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.NatAsAlmostRing using (ℕAsAlmostRing)
open import Cubical.Algebra.RingSolver.IntAsRawRing

private
  variable
    ℓ ℓ′ : Level

record RawAlgebra (R : RawRing {ℓ}) (ℓ′ : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where

  constructor rawalgebra

  field
    Carrier : Type ℓ′
    scalar  : ⟨ R ⟩ᵣ → Carrier
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ : {R : RawRing {ℓ}} → RawAlgebra R ℓ′ → Type ℓ′
⟨_⟩ = RawAlgebra.Carrier

private
  ℕAsRawRing = AlmostRing→RawRing ℕAsAlmostRing

AlmostRing→RawℕAlgebra : AlmostRing {ℓ} → RawAlgebra ℕAsRawRing ℓ
AlmostRing→RawℕAlgebra (almostring A 0r 1r _+_ _·_ -_ isAlmostRing) =
  rawalgebra A scalar 0r 1r _+_ _·_ -_
  where
    scalar : ℕ → A
    scalar ℕ.zero = 0r
    scalar (ℕ.suc ℕ.zero) = 1r
    scalar (ℕ.suc (ℕ.suc n)) = 1r + scalar (ℕ.suc n)

AlmostRing→RawℤAlgebra : AlmostRing {ℓ} → RawAlgebra ℤAsRawRing ℓ
AlmostRing→RawℤAlgebra (almostring A 0r 1r _+_ _·_ -_ isAlmostRing) =
  rawalgebra A scalar 0r 1r _+_ _·_ -_
  where
    -- helper variable (k : ℕ) for termination checking
    scalar' : ℕ → ℤ → A
    scalar' k (pos ℕ.zero) = 0r
    scalar' k (pos (ℕ.suc ℕ.zero)) = 1r
    scalar' k (pos (ℕ.suc (ℕ.suc n))) = 1r + scalar' k (pos (ℕ.suc n))
    scalar' ℕ.zero (negsuc n) = 0r
    scalar' (ℕ.suc k) (negsuc n) = - (scalar' k (pos (ℕ.suc n)))

    scalar : ℤ → A
    scalar (pos k)  = scalar' ℕ.zero (pos k)
    scalar (negsuc k)  = scalar' (ℕ.suc k) (negsuc k)

    test : scalar (negsuc (ℕ.suc ℕ.zero)) ≡ -(1r + 1r)
    test = refl
