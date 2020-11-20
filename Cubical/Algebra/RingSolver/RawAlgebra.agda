{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RawAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.RingSolver.AlmostRing hiding (⟨_⟩)
open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.NatAsAlmostRing using (ℕAsAlmostRing)

private
  variable
    ℓ ℓ′ : Level

record RawAlgebra (R : RawRing {ℓ′}) : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where

  constructor rawalgebra

  field
    Carrier : Type ℓ
    scalar  : ⟨ R ⟩ → Carrier
    0r      : Carrier
    1r      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  infixl 8 _·_
  infixl 7 -_
  infixl 6 _+_

⟨_⟩ₐ : {R : RawRing {ℓ′}} → RawAlgebra R → Type ℓ
⟨_⟩ₐ = RawAlgebra.Carrier

private
  ℕAsRawRing = AlmostRing→RawRing ℕAsAlmostRing

AlmostRing→RawℕAlgebra : AlmostRing {ℓ} → RawAlgebra {ℓ = ℓ} ℕAsRawRing
AlmostRing→RawℕAlgebra (almostring A 0r 1r _+_ _·_ -_ isAlmostRing) =
  rawalgebra A inclusion 0r 1r _+_ _·_ -_
  where
    inclusion : ℕ → A
    inclusion ℕ.zero = 0r
    inclusion (ℕ.suc n) = 1r + inclusion n
