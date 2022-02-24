{-# OPTIONS --safe #-}
module Cubical.Syntax.⟨⟩ where

open import Cubical.Core.Primitives

-- A syntax typeclass for types which contain a "carrier" type in the
-- sence of an algebraic structure.
record has-⟨⟩ {ℓᵢ ℓ₂} (Instance : Type ℓᵢ) (Instance2 : Type ℓ₂) : Type (ℓ-max ℓᵢ (ℓ-suc ℓ₂)) where
  field
    ⟨_⟩ : Instance → Instance2

open has-⟨⟩ ⦃ … ⦄ public
