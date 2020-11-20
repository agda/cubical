{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.AlgebraHornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)

open import Cubical.Algebra.RingSolver.RawRing
open import Cubical.Algebra.RingSolver.RawAlgebra
open import Cubical.Algebra.RingSolver.AlmostRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

private
  variable
    ℓ ℓ′ : Level

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

data IteratedHornerForms {R : RawRing {ℓ}} (A : RawAlgebra R ℓ′) : ℕ → Type ℓ where
  const : ⟨ R ⟩ → IteratedHornerForms A ℕ.zero
  0H : {n : ℕ} → IteratedHornerForms A (ℕ.suc n)
  _·X+_ : {n : ℕ} → IteratedHornerForms A (ℕ.suc n) → IteratedHornerForms A n
                  → IteratedHornerForms A (ℕ.suc n)

Eval : {R : RawRing {ℓ}} {A : RawAlgebra R ℓ′}
       (n : ℕ) (P : IteratedHornerForms A n)
       → Vec ⟨ A ⟩ₐ n → ⟨ A ⟩ₐ
Eval {A = A} ℕ.zero (const r) [] = RawAlgebra.scalar A r
Eval {A = A} .(ℕ.suc _) 0H (_ ∷ _) = RawAlgebra.0r A
Eval {A = A} (ℕ.suc n) (P ·X+ Q) (x ∷ xs) =
  let open RawAlgebra A
  in (Eval (ℕ.suc n) P (x ∷ xs)) · x + Eval n Q xs

module IteratedHornerOperations {R : RawRing {ℓ}} (A : RawAlgebra R ℓ′) where
  open RawRing R

  private
    1H' : (n : ℕ) → IteratedHornerForms A n
    1H' ℕ.zero = const 1r
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms A n
    0H' ℕ.zero = const 0r
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms A n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms A n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms A n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
               → IteratedHornerForms A n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) = (P +ₕ Q) ·X+ (r +ₕ s)

  -ₕ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
  -ₕ (const x) = const (- x)
  -ₕ 0H = 0H
  -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

  isZero : {n : ℕ} → IteratedHornerForms A (ℕ.suc n)
                   → Bool
  isZero 0H = true
  isZero (P ·X+ P₁) = false

  _⋆_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A (ℕ.suc n)
                → IteratedHornerForms A (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms A n → IteratedHornerForms A n
                → IteratedHornerForms A n
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

  asRawRing : (n : ℕ) → RawRing {ℓ}
  RawRing.Carrier (asRawRing n) = IteratedHornerForms A n
  RawRing.0r (asRawRing n) = 0ₕ
  RawRing.1r (asRawRing n) = 1ₕ
  RawRing._+_ (asRawRing n) = _+ₕ_
  RawRing._·_ (asRawRing n) = _·ₕ_
  RawRing.- (asRawRing n) =  -ₕ

Variable : (n : ℕ) {R : RawRing {ℓ}} (A : RawAlgebra R ℓ′) (k : Fin n) → IteratedHornerForms A n
Variable n R k = IteratedHornerOperations.X R n k

Constant : (n : ℕ) {R : RawRing {ℓ}} (A : RawAlgebra R ℓ′) (r : ⟨ R ⟩) → IteratedHornerForms A n
Constant ℕ.zero R r = const r
Constant (ℕ.suc n) R r = IteratedHornerOperations.0ₕ R ·X+ Constant n R r
