{-# OPTIONS --safe #-}
module Cubical.Data.Empty.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level

data ⊥ : Type₀ where

⊥* : Type ℓ
⊥* = Lift ⊥

rec : {A : Type ℓ} → ⊥ → A
rec ()

elim : {A : ⊥ → Type ℓ} → (x : ⊥) → A x
elim ()
