{-

This file contains:

- Definition of set truncations

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SetTruncation.Base where

open import Cubical.Core.Primitives

-- set truncation as a higher inductive type:

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ (x y : ∥ A ∥₂) (p q : x ≡ y) → p ≡ q
