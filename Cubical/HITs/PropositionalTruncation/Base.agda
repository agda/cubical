{-

This file contains:

- Definition of propositional truncation

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.PropositionalTruncation.Base where

open import Cubical.Core.Primitives

-- Propositional truncation as a higher inductive type:

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y


-- Mere existence

∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ∥ Σ A B ∥

infix 2 ∃-syntax

∃-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
