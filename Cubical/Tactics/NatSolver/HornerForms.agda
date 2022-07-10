{-# OPTIONS --safe #-}
module Cubical.Tactics.NatSolver.HornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat hiding (isZero)
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)

private
  variable
    ℓ : Level

{-
  This defines the type of multivariate Polynomials over ℕ.
  The construction is based on the algebraic fact

    ℕ[X₀][X₁]⋯[Xₙ] ≅ ℕ[X₀,⋯,Xₙ]

  BUT: Contrary to algebraic convetions, we will give 'Xₙ' the lowest index
  in the definition of 'Variable' below. So if 'Variable n k' is identified
  with 'Xₖ', what we construct should rather be denoted with

    ℕ[Xₙ][Xₙ₋₁]⋯[X₀]

  or, to be precise about the evaluation order:

    (⋯((ℕ[Xₙ])[Xₙ₋₁])⋯)[X₀]

-}

data IteratedHornerForms : ℕ → Type ℓ-zero where
  const : ℕ → IteratedHornerForms ℕ.zero
  0H : {n : ℕ} → IteratedHornerForms (ℕ.suc n)
  _·X+_ : {n : ℕ} → IteratedHornerForms (ℕ.suc n) → IteratedHornerForms n
                  → IteratedHornerForms (ℕ.suc n)

eval : {n : ℕ} (P : IteratedHornerForms n)
       → Vec ℕ n → ℕ
eval (const r) [] = r
eval 0H (_ ∷ _) = 0
eval (P ·X+ Q) (x ∷ xs) =
  (eval P (x ∷ xs)) · x + eval Q xs

module IteratedHornerOperations where

  private
    1H' : (n : ℕ) → IteratedHornerForms n
    1H' ℕ.zero = const 1
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms n
    0H' ℕ.zero = const 0
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
               → IteratedHornerForms n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) = (P +ₕ Q) ·X+ (r +ₕ s)

  isZero : {n : ℕ} → IteratedHornerForms (ℕ.suc n)
                   → Bool
  isZero 0H = true
  isZero (P ·X+ P₁) = false

  _⋆_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms (ℕ.suc n)
                → IteratedHornerForms (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
                → IteratedHornerForms n
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

Variable : (n : ℕ) (k : Fin n) → IteratedHornerForms n
Variable n k = IteratedHornerOperations.X n k

Constant : (n : ℕ) (r : ℕ) → IteratedHornerForms n
Constant ℕ.zero r = const r
Constant (ℕ.suc n) r = IteratedHornerOperations.0ₕ ·X+ Constant n r
