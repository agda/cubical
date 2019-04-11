{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Empty.Base where

open import Cubical.Core.Everything

data ⊥ : Type₀ where

⊥-elim : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
⊥-elim ()

