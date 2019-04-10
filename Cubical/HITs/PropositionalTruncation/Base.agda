{-

This file contains:

- Definition of propositional truncation

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.PropositionalTruncation.Base where

open import Cubical.Core.Prelude

-- Propositional truncation as a higher inductive type:

data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y
