{- Basic definitions using Σ-types

Σ-types are defined in Core/Primitives as they are needed for Glue types.

The file contains:

- Non-dependent pair types: A × B
- Mere existence: ∃[x ∈ A] B
- Unique existence: ∃![x ∈ A] B

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Sigma.Base where

open import Cubical.Core.Primitives public

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base


-- Non-dependent pair types

_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infixr 5 _×_


-- Mere existence

∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ∥ Σ A B ∥₁

infix 2 ∃-syntax

∃-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B


-- Unique existence

∃! : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃! A B = isContr (Σ A B)

infix 2 ∃!-syntax

∃!-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃!-syntax = ∃!

syntax ∃!-syntax A (λ x → B) = ∃![ x ∈ A ] B
