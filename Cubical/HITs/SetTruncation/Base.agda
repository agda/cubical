{-

This file contains:

- Definition of set truncations

-}
module Cubical.HITs.SetTruncation.Base where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Pointed

-- set truncation as a higher inductive type:

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ (x y : ∥ A ∥₂) (p q : x ≡ y) → p ≡ q

-- Pointed version
∥_∥₂∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
fst ∥ A ∥₂∙ = ∥ fst A ∥₂
snd ∥ A ∥₂∙ = ∣ pt A ∣₂
