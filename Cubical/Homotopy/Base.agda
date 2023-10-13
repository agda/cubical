{-# OPTIONS --safe #-}

module Cubical.Homotopy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Properties

private
  variable
    ℓ ℓ' a b c : Level
    A : Type a
    B : Type b
    C : Type c

infix 4 _∼_
_∼_ : {X : Type ℓ} {Y : X → Type ℓ'} → (f g : (x : X) → Y x) → Type (ℓ-max ℓ ℓ')
_∼_ {X = X} f g = (x : X) → f x ≡ g x

funExt∼ : {X : Type ℓ} {Y : X → Type ℓ'} {f g : (x : X) → Y x} (H : f ∼ g) → f ≡ g
funExt∼ = funExt

∼-refl : {X : Type ℓ} {Y : X → Type ℓ'} {f : (x : X) → Y x} → f ∼ f
∼-refl {f = f} = λ x → refl {x = f x}

infixr 30 _▪_
infixr 35 _▪ˡ_ _▪ʳ_
_▪_ : {P : A → Type ℓ} {f g h : (a : A) → P a} → (f ∼ g) → (g ∼ h) → f ∼ h
(α ▪ β) x = α x ∙ β x

_▪ˡ_ : (f : B → C) {g h : A → B} → g ∼ h → f ∘ g ∼ f ∘ h
(f ▪ˡ α) x = cong f (α x)

_▪ʳ_ : {f g : B → C} → f ∼ g → (h : A → B) → f ∘ h ∼ g ∘ h
(α ▪ʳ h) x = α (h x)
