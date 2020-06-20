{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Homotopy.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Properties


private
  variable
    ℓ ℓ' ℓ'' : Level

_∼_ : {X : Type ℓ} {Y : X → Type ℓ'} → (f g : (x : X) → Y x) → Type (ℓ-max ℓ ℓ')
_∼_ {X = X} f g = (x : X) → f x ≡ g x

funExt∼ : {X : Type ℓ} {Y : X → Type ℓ'} {f g : (x : X) → Y x} (H : f ∼ g) → f ≡ g
funExt∼ H = funExt H

∼-refl : {X : Type ℓ} {Y : X → Type ℓ'} {f : (x : X) → Y x} → f ∼ f
∼-refl {f = f} = λ x → refl {x = f x}
