{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.MultivariatePolynomials where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.AlmostRing renaming (⟨_⟩ to ⟨_⟩ᵣ)
open import Cubical.Algebra.RingSolver.HornerNormalForm

private
  variable
    ℓ : Level


{-
  This defines the type of multivariate Polynomials over the RawRing R.
  The construction is based on the algebraic fact

    R[X₀][X₁]⋯[Xₙ] ≅ R[X₀,⋯,Xₙ]

  BUT: Contrary to algebraic convetions, we will give 'Xₙ' the lowest index
  in the definition of 'Variable' below. So if 'Variable n R k' is identified
  with 'Xₖ', then the RawRing we construct should rather be denoted with

    R[Xₙ][Xₙ₋₁]⋯[X₀]

  or, to be precise about the evaluation order:

    (⋯((R[Xₙ])[Xₙ₋₁])⋯)[X₀]

-}
data IteratedHornerForms (R : RawRing {ℓ}) : ℕ → Type ℓ where
  const : ⟨ R ⟩ → IteratedHornerForms R ℕ.zero
  0H : {n : ℕ} → IteratedHornerForms R n
  _·X+_ : {n : ℕ} → IteratedHornerForms R (ℕ.suc n) → IteratedHornerForms R n
                  → IteratedHornerForms R (ℕ.suc n)

Eval : {R : RawRing {ℓ}} (n : ℕ) (P : IteratedHornerForms R n)
             → Vec ⟨ R ⟩ n → ⟨ R ⟩
Eval ℕ.zero (const r) [] = r
Eval {R = R} .ℕ.zero 0H [] = RawRing.0r R
Eval {R = R} .(ℕ.suc _) 0H (_ ∷ _) = RawRing.0r R
Eval {R = R} (ℕ.suc n) (P ·X+ Q) (x ∷ xs) =
  let open RawRing R
  in (Eval (ℕ.suc n) P (x ∷ xs)) · x + Eval n Q xs

module IteratedHornerOperations (R : RawRing {ℓ}) where
  open RawRing R

  1H : IteratedHornerForms R 0
  1H = const 1r

  X : IteratedHornerForms R 1
  X = (0H ·X+ (const 1r)) ·X+ (const 0r)

  _+H_ : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R n
               → IteratedHornerForms R n
  (const r) +H (const s) = const (r + s)
  (const r) +H 0H = const r
  0H +H Q = Q
  (P ·X+ r) +H 0H = P ·X+ r
  (P ·X+ r) +H (Q ·X+ s) = (P +H Q) ·X+ (r +H s)

  -H : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R n
  -H (const x) = const (- x)
  -H 0H = 0H
  -H (P ·X+ Q) = (-H P) ·X+ (-H Q)
