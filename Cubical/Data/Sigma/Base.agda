{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Base where

open import Cubical.Core.Primitives public

-- Σ-types are defined in Core/Primitives as they are needed for Glue types.


_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infixr 5 _×_
