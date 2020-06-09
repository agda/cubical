{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Empty.Base where

open import Cubical.Core.Everything

data ⊥ : Type₀ where

rec : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
rec ()

elim : ∀ {ℓ} {A : ⊥ → Type ℓ} → (x : ⊥) → A x
elim ()
