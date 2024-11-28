{-

This file introduces the "powerset" of a type in the style of
Escardó's lecture notes:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#propositionalextensionality

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

ℙ : Type ℓ → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
ℙ X ℓ' = X → hProp ℓ'

isSetℙ : isSet (ℙ X ℓ')
isSetℙ = isSetΠ λ x → isSetHProp

infix 5 _∈_

_∈_ : {X : Type ℓ} → X → ℙ X ℓ' → Type ℓ'
x ∈ A = ⟨ A x ⟩

_⊆_ : {X : Type ℓ} → ℙ X ℓ' → ℙ X ℓ' → Type (ℓ-max ℓ ℓ')
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-isProp : (A : ℙ X _) (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

⊆-isProp : (A B : ℙ X _) → isProp (A ⊆ B)
⊆-isProp A B = isPropΠ2 (λ x _ → ∈-isProp B x)

⊆-refl : (A : ℙ X _) → A ⊆ A
⊆-refl A x = idfun (x ∈ A)

subst-∈ : (A : ℙ X _) {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl-consequence : (A B : ℙ X _) → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : ℙ X _) → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) (φ x) (ψ x)))

⊆-extensionalityEquiv : (A B : ℙ X _) → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSetℙ A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))
