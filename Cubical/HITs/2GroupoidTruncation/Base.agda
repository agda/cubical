{-

This file contains:

- Definition of 2-groupoid truncations

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.2GroupoidTruncation.Base where

open import Cubical.Foundations.Prelude

-- 2-groupoid truncation as a higher inductive type:

data ∥_∥₂ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ (x y : ∥ A ∥₂) (p q : x ≡ y) (r s : p ≡ q) (t u : r ≡ s) → t ≡ u
