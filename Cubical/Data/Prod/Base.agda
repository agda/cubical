{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Prod.Base where

open import Cubical.Core.Everything

infixr 5 _×_

_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)
