{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.HornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)

open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.AlmostRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

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

data IteratedHornerForms (R : RawRing ℓ) : ℕ → Type ℓ where
  const : ⟨ R ⟩ → IteratedHornerForms R ℕ.zero
  0H : {n : ℕ} → IteratedHornerForms R (ℕ.suc n)
  _·X+_ : {n : ℕ} → IteratedHornerForms R (ℕ.suc n) → IteratedHornerForms R n
                  → IteratedHornerForms R (ℕ.suc n)

eval : {R : RawRing ℓ} (n : ℕ) (P : IteratedHornerForms R n)
             → Vec ⟨ R ⟩ n → ⟨ R ⟩
eval ℕ.zero (const r) [] = r
eval {R = R} .(ℕ.suc _) 0H (_ ∷ _) = RawRing.0r R
eval {R = R} (ℕ.suc n) (P ·X+ Q) (x ∷ xs) =
  let open RawRing R
  in (eval (ℕ.suc n) P (x ∷ xs)) · x + eval n Q xs

module IteratedHornerOperations (R : RawRing ℓ) where
  open RawRing R

  private
    1H' : (n : ℕ) → IteratedHornerForms R n
    1H' ℕ.zero = const 1r
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms R n
    0H' ℕ.zero = const 0r
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms R n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms R n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms R n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R n
               → IteratedHornerForms R n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) = (P +ₕ Q) ·X+ (r +ₕ s)

  -ₕ : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R n
  -ₕ (const x) = const (- x)
  -ₕ 0H = 0H
  -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

  isZero : {n : ℕ} → IteratedHornerForms R (ℕ.suc n)
                   → Bool
  isZero 0H = true
  isZero (P ·X+ P₁) = false

  _⋆_ : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R (ℕ.suc n)
                → IteratedHornerForms R (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms R n → IteratedHornerForms R n
                → IteratedHornerForms R n
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ Q) = (r ⋆ P) ·X+ (r ·ₕ Q)

  const x ·ₕ const y = const (x · y)
  0H ·ₕ Q = 0H
  (P ·X+ Q) ·ₕ S =
     let
        z = (P ·ₕ S)
     in if (isZero z)
        then (Q ⋆ S)
        else (z ·X+ 0ₕ) +ₕ (Q ⋆ S)

  asRawRing : (n : ℕ) → RawRing ℓ
  RawRing.Carrier (asRawRing n) = IteratedHornerForms R n
  RawRing.0r (asRawRing n) = 0ₕ
  RawRing.1r (asRawRing n) = 1ₕ
  RawRing._+_ (asRawRing n) = _+ₕ_
  RawRing._·_ (asRawRing n) = _·ₕ_
  RawRing.- (asRawRing n) =  -ₕ

Variable : (n : ℕ) (R : RawRing ℓ) (k : Fin n) → IteratedHornerForms R n
Variable n R k = IteratedHornerOperations.X R n k

Constant : (n : ℕ) (R : RawRing ℓ) (r : ⟨ R ⟩) → IteratedHornerForms R n
Constant ℕ.zero R r = const r
Constant (ℕ.suc n) R r = IteratedHornerOperations.0ₕ R ·X+ Constant n R r
