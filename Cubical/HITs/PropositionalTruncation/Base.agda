{-

This file contains:

- Definition of propositional truncation

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.PropositionalTruncation.Base where

open import Cubical.Core.Primitives

-- Propositional truncation as a higher inductive type:

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y
