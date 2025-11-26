module Cubical.Data.Empty.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

data ⊥ : Type₀ where

⊥* : ∀ {ℓ} → Type ℓ
⊥* = Lift _ ⊥

rec : {A : Type ℓ} → ⊥ → A
rec ()

rec* : {A : Type ℓ} → ⊥* {ℓ'} → A
rec* ()

elim : {A : ⊥ → Type ℓ} → (x : ⊥) → A x
elim ()

elim* : {A : ⊥* {ℓ'} → Type ℓ} → (x : ⊥*) → A x
elim* ()
