{-

This file contains:

- Definition of groupoid truncations

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.GroupoidTruncation.Base where

open import Cubical.Core.Primitives

-- groupoid truncation as a higher inductive type:

data ∥_∥₃ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₃ : A → ∥ A ∥₃
  squash₃ : ∀ (x y : ∥ A ∥₃) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s
