{-

The Inductive Version of James Construction

This file contains:
  - An inductive construction of James and its equivalence to the non-inductive version.
    (KANG Rongji, Feb. 2022)

This file is the summary of the main results.
The proof is divided into parts and put inside the fold Cubical.HITs.James.Inductive

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.James.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Cubical.HITs.James.Base
open import Cubical.HITs.James.Inductive.Base
open import Cubical.HITs.James.Inductive.PushoutFormula
open import Cubical.HITs.James.Inductive.Reduced
open import Cubical.HITs.James.Inductive.ColimitEquivalence

private
  variable
    ℓ : Level

module JamesInd
  (X∙@(X , x₀) : Pointed ℓ) where

  -- The follwing 𝕁 n is equivalence to Brunerie's family J n, as will be shown latter.
  -- Instead of his inductive procedure, 𝕁 is defined directly as an indexed HIT.

  𝕁 : ℕ → Type ℓ
  𝕁 = 𝕁ames (X , x₀)

  -- The type 𝕁∞ is the direct colimit of 𝕁.

  𝕁∞ : Type ℓ
  𝕁∞ = 𝕁ames∞ (X , x₀)

  -- And it is equivalent to James.

  J≃𝕁∞ : James (X , x₀) ≃ 𝕁∞
  J≃𝕁∞ = compEquiv (James≃𝕁Red∞ _) (invEquiv (𝕁ames∞≃𝕁Red∞ _))

  -- Description of 𝕁 n for n = 0, 1 and 2

  𝕁₀≃Unit : 𝕁 0 ≃ Unit
  𝕁₀≃Unit = 𝕁ames0≃ _

  𝕁₁≃X : 𝕁 1 ≃ X
  𝕁₁≃X = 𝕁ames1≃ _

  𝕁₂≃P[X×X←X⋁X→X] : 𝕁 2 ≃ Pushout ⋁↪ fold⋁
  𝕁₂≃P[X×X←X⋁X→X] = 𝕁ames2≃ _

  -- The following family is defined as pushouts of 𝕁 n.

  𝕁Push : ℕ → Type ℓ
  𝕁Push = 𝕁amesPush (X , x₀)

  -- Brunerie uses f and g to denote the following maps, so do I.

  module _
    {n : ℕ} where

    f : 𝕁Push n → X × 𝕁 (1 + n)
    f = leftMap _

    g : 𝕁Push n → 𝕁 (1 + n)
    g = rightMap _

  -- The following equivalence shows 𝕁(n+2) can be made as double pushouts invoving only X, 𝕁 n and 𝕁(n+1).
  -- So our 𝕁 is exactly what Brunerie has defined.

  𝕁ₙ₊₂≃Pushout : (n : ℕ) → 𝕁 (2 + n) ≃ Pushout f g
  𝕁ₙ₊₂≃Pushout = 𝕁ames2+n≃ _
