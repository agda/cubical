{-

This file contains:

- Definition of propositional truncation

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.PropositionalTruncation.Base where

open import Cubical.Core.Primitives

-- Propositional truncation as a higher inductive type:

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁ : A → ∥ A ∥₁
  squash₁ : ∀ (x y : ∥ A ∥₁) → x ≡ y
