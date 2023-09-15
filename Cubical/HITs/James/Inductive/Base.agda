{-

This file contains:
  - The inductive construction of James.

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat

open import Cubical.HITs.SequentialColimit

private
  variable
    ℓ : Level

module _
  (X∙@(X , x₀) : Pointed ℓ) where

  -- The family 𝕁ames n is equivalence to Brunerie's J n

  data 𝕁ames : ℕ → Type ℓ where
    [] : 𝕁ames 0
    _∷_   : {n : ℕ} → X → 𝕁ames n → 𝕁ames (1 + n)
    incl  : {n : ℕ} → 𝕁ames n → 𝕁ames (1 + n)
    incl∷ : {n : ℕ} → (x : X)(xs : 𝕁ames n) → incl (x ∷ xs) ≡ x ∷ incl xs
    unit  : {n : ℕ} → (xs : 𝕁ames n) → incl xs ≡ x₀ ∷ xs
    coh   : {n : ℕ} → (xs : 𝕁ames n) → PathP (λ i → incl (unit xs i) ≡ x₀ ∷ incl xs) (unit (incl xs)) (incl∷ x₀ xs)

  -- The direct system defined by 𝕁ames

  open Sequence

  𝕁amesSeq : Sequence ℓ
  𝕁amesSeq .obj = 𝕁ames
  𝕁amesSeq .map = incl

  -- The 𝕁ames∞ wanted is the direct colimit of 𝕁ames n

  𝕁ames∞ : Type ℓ
  𝕁ames∞ = SeqColim 𝕁amesSeq
