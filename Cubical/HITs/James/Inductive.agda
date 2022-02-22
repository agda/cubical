{-

This file contains:
  - The inductive construction of James and its equivalence to the non-inductive version.
    (KANG Rongji, Feb. 2022)

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout

open import Cubical.HITs.James.Base
open import Cubical.HITs.James.Inductive.Base
open import Cubical.HITs.James.Inductive.PushoutFormula
open import Cubical.HITs.James.Inductive.Reduced
  hiding (𝕁 ; 𝕁∞)
open import Cubical.HITs.James.Inductive.ColimitEquivalence


private
  variable
    ℓ : Level

module _
  ((X , x₀) : Pointed ℓ) where

  𝕁 : ℕ → Type ℓ
  𝕁 = 𝕁ames (X , x₀)

  𝕁∞ : Type ℓ
  𝕁∞ = 𝕁ames∞ (X , x₀)

  J≃𝕁∞ : James (X , x₀) ≃ 𝕁∞
  J≃𝕁∞ = compEquiv (James≃𝕁Red∞ _) (invEquiv (𝕁ames∞≃𝕁Red∞ _))

  𝕁₀≃Unit : 𝕁 0 ≃ Unit
  𝕁₀≃Unit = 𝕁ames0≃ _

  𝕁₁≃X : 𝕁 1 ≃ X
  𝕁₁≃X = 𝕁ames1≃ _

  𝕁Push : ℕ → Type ℓ
  𝕁Push = Push𝕁ames (X , x₀)

  module _
    {n : ℕ} where

    f : 𝕁Push n → X × 𝕁 (1 + n)
    f = leftMap _

    g : 𝕁Push n → 𝕁 (1 + n)
    g = rightMap _

  𝕁ₙ₊₂≃Pushout : (n : ℕ) → 𝕁 (2 + n) ≃ Pushout f g
  𝕁ₙ₊₂≃Pushout = 𝕁ames2+n≃ _

