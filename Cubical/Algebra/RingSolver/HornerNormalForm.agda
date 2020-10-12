{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.HornerNormalForm where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Algebra.RingSolver.RawRing

private
  variable
    ℓ : Level

data RawHornerPolynomial (R : RawRing {ℓ}) : Type ℓ where
  0H : RawHornerPolynomial R
  _·X+_ : RawHornerPolynomial R → ⟨ R ⟩ → RawHornerPolynomial R

module HornerOperations (R : RawRing {ℓ}) where
  open RawRing R

  1H : RawHornerPolynomial R
  1H = 0H ·X+ 1r

  X : RawHornerPolynomial R
  X = 1H ·X+ 0r

  _+H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H +H Q = Q
  (P ·X+ r) +H 0H = P ·X+ r
  (P ·X+ r) +H (Q ·X+ s) = (P +H Q) ·X+ (r + s)

  _⋆_ : ⟨ R ⟩ → RawHornerPolynomial R → RawHornerPolynomial R
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ s) = (r ⋆ P) ·X+ (r · s)

  _·H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H ·H _ = 0H
  (P ·X+ r) ·H Q = ((P ·H Q) ·X+ 0r) +H (r ⋆ Q)

  -H_ : RawHornerPolynomial R → RawHornerPolynomial R
  -H 0H = 0H
  -H (P ·X+ r) = (-H P) ·X+ (- r)

  evalH : RawHornerPolynomial R → ⟨ R ⟩ → ⟨ R ⟩
  evalH 0H x₀ = 0r
  evalH (P ·X+ r) x₀ = (evalH P x₀) · x₀ + r

  asRawRing : RawRing {ℓ}
  RawRing.Carrier asRawRing = RawHornerPolynomial R
  RawRing.0r asRawRing = 0H
  RawRing.1r asRawRing = 0H ·X+ 1r
  RawRing._+_ asRawRing = _+H_
  RawRing._·_ asRawRing = _·H_
  RawRing.- asRawRing =  -H_

{-
IteratedHornerPolynomials : (n : ℕ) (R : RawRing {ℓ}) → Type ℓ
IteratedHornerPolynomials = {!!}
-}
