{-# OPTIONS --safe #-}
module Cubical.Syntax.⟨⟩ where

open import Cubical.Core.Primitives

-- A syntax typeclass for types which contain a "carrier" type in the
-- sence of an algebraic structure.
record has-⟨⟩ {ℓᵢ ℓc} (Instance : Type ℓᵢ) : Type (ℓ-max ℓᵢ (ℓ-suc ℓc)) where
  field
    ⟨_⟩ : Instance → Type ℓc

open has-⟨⟩ ⦃ … ⦄ public
