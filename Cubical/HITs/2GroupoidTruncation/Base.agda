{-

This file contains:

- Definition of 2-groupoid truncations

-}
module Cubical.HITs.2GroupoidTruncation.Base where

open import Cubical.Foundations.Prelude

-- 2-groupoid truncation as a higher inductive type:

data ∥_∥₄ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₄ : A → ∥ A ∥₄
  squash₄ : ∀ (x y : ∥ A ∥₄) (p q : x ≡ y) (r s : p ≡ q) (t u : r ≡ s) → t ≡ u
