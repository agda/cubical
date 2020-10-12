{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.MultivariatePolynomials where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec

open import Cubical.Algebra.RingSolver.RawRing
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
IteratedHornerForms : (n : ℕ) (R : RawRing {ℓ}) → RawRing {ℓ}
IteratedHornerForms ℕ.zero    R = R
IteratedHornerForms (ℕ.suc n) R = HornerOperations.asRawRing
                                          (IteratedHornerForms n R)

Variable : (n : ℕ) (R : RawRing {ℓ}) (k : Fin n) → ⟨ IteratedHornerForms n R ⟩
Variable ℕ.zero R ()
Variable (ℕ.suc m) R zero = HornerOperations.X (IteratedHornerForms m R)
Variable (ℕ.suc m) R (suc k) = HornerOperations.Const
                                 (IteratedHornerForms m R)
                                 (Variable m R k)

Constant : (n : ℕ) (R : RawRing {ℓ}) (r : ⟨ R ⟩) → ⟨ IteratedHornerForms n R ⟩
Constant ℕ.zero R r = r
Constant (ℕ.suc n) R r = HornerOperations.Const (IteratedHornerForms n R) (Constant n R r)

private
  EvaluateExplicit : (n : ℕ) (R : RawRing {ℓ}) (P : ⟨ IteratedHornerForms n R ⟩)
             → Vec ⟨ R ⟩ n → ⟨ R ⟩
  EvaluateExplicit ℕ.zero R r [] = r
  EvaluateExplicit (ℕ.suc m) R P (x ∷ xs) =
    EvaluateExplicit m R
      (HornerOperations.evalH (IteratedHornerForms m R) P (Constant m R x))
      xs

Evaluate : {n : ℕ} {R : RawRing {ℓ}} (P : ⟨ IteratedHornerForms n R ⟩)
             → Vec ⟨ R ⟩ n → ⟨ R ⟩
Evaluate {ℓ} {n} {R} = EvaluateExplicit n R
