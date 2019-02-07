{-

This file contains:

- Definition of set truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetTruncation.Base where

open import Cubical.Core.Prelude

-- set truncation as a higher inductive type:

data ∥_∥₀ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣₀ : A → ∥ A ∥₀
  squash₀ : ∀ (x y : ∥ A ∥₀) (p q : x ≡ y) → p ≡ q
