{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Empty.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

data ⊥ : Type₀ where

⊥* : ∀ {ℓ} → Type ℓ
⊥* = Lift ⊥

rec : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
rec ()

elim : ∀ {ℓ} {A : ⊥ → Type ℓ} → (x : ⊥) → A x
elim ()
