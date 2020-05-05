{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.Family where

open import Cubical.Foundations.Logic
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

private
  variable
    ℓ₀ ℓ₁ ℓ₂ : Level

Fam : (ℓ₀ : Level) → Type ℓ₁ → Type (ℓ-max (ℓ-suc ℓ₀) ℓ₁)
Fam ℓ A = Σ (Set ℓ) (λ I → I → A)

index : {A : Type ℓ₀} → Fam ℓ₁ A → Type ℓ₁
index (I , _) = I

-- Application of a family over X to an index.
_$_ : {A : Type ℓ₀} → (ℱ : Fam ℓ₂ A) → index ℱ → A
_$_ (_ , f) = f

infixr 7 _$_

-- Membership for families.
_ε_ : {A : Type ℓ₀} → A → Fam ℓ₁ A → Type _
x ε (_ , f) = fiber f x

-- Composition of a family with a function.
_⟨$⟩_ : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
g ⟨$⟩ ℱ = (index ℱ) , λ x → g (ℱ $ x)

fmap : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
fmap = _⟨$⟩_

syntax fmap (λ x → e) ℱ = ⁅ e ∣ x ε ℱ ⁆

compri : {X : Type ℓ₀} → (I : Type ℓ₂) → (I → X) → Fam ℓ₂ X
compri I f = (I , f)

syntax compri I (λ i → e) = ⁅ e ∣ i ∶ I ⁆

-- Forall quantification for families.
fam-forall : {A : Type ℓ₀} (ℱ : Fam ℓ₂ A) → (A → hProp ℓ₁) → hProp _
fam-forall {A = A} ℱ P = ((x : A) → x ε ℱ → [ P x ]) , prop
  where
    prop : isProp ((x : A) → x ε ℱ → [ P x ])
    prop = isPropΠ2 λ x _ → snd (P x)

syntax fam-forall ℱ (λ x → P) = ∀[ x ε ℱ ] P

-- Familification of a given powerset.
⟪_⟫ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Fam (ℓ-max ℓ₀ ℓ₁) A
⟪_⟫ {A = A} U = (Σ[ x ∈ A ] [ U x ]) , fst
