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
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Relation.Nullary using (¬_)

private
  variable
    ℓ : Level
    X : Type ℓ

ℙ : Type ℓ → Type (ℓ-suc ℓ)
ℙ X = X → hProp _

isSetℙ : isSet (ℙ X)
isSetℙ = isSetΠ λ x → isSetHProp

infix 5 _∈_

_∈_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∈ A = ⟨ A x ⟩

_⊆_ : {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-isProp : (A : ℙ X) (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

infix 5 _∈ₚ_

-- x ∈ₚ A differs from x ∈ A
-- in the sense that it produces an hProp
_∈ₚ_ : {X : Type ℓ} → X → ℙ X → hProp ℓ
x ∈ₚ A = x ∈ A , ∈-isProp A x

-- "not in" relations

infix 5 _∉_
_∉_ : {X : Type ℓ} → X → ℙ X → Type ℓ
x ∉ A = ¬ x ∈ A

∉-isProp : (A : ℙ X) (x : X) → isProp (x ∉ A)
∉-isProp A x = isPropΠ λ _ → isProp⊥

infix 5 _∉ₚ_
_∉ₚ_ : {X : Type ℓ} → X → ℙ X → hProp ℓ
x ∉ₚ A = x ∉ A , ∉-isProp A x

⊆-isProp : (A B : ℙ X) → isProp (A ⊆ B)
⊆-isProp A B = isPropΠ2 (λ x _ → ∈-isProp B x)

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl A x = idfun (x ∈ A)

subst-∈ : (A : ℙ X) {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl-consequence : (A B : ℙ X) → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : ℙ X) → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) (φ x) (ψ x)))

⊆-extensionalityEquiv : (A B : ℙ X) → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSetℙ A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))

-- Binary Intersections
infix 6 _∩_

-- Unfortunately, simply importing Cubical.Data.Sum, Cubical.HITs.PropositionalTruncation and
-- Cubical.Functions.Logic indirectly imports Cubical.Functions.Embeddings which
-- creates a circular dependency
-- For now, we will have to repeat a few definitions
-- We mark all these as private to ensure that no name clashes take place

_∩_ : ℙ X → ℙ X → ℙ X
A ∩ B = λ x → A x ⊓ B x where
              -- Repeated from Cubical.Functions.Logic
              _⊓_ : hProp ℓ → hProp ℓ → hProp ℓ
              a ⊓ b = ⟨ a ⟩ × ⟨ b ⟩ , isOfHLevelΣ 1 (a .snd) λ _ → b .snd 

-- Repeated from Cubical.Data.Sum
private data _⊎_ (A B : Type ℓ) : Type ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Repeated from Cubical.Functions.Logic
∥_∥ₚ : (X : Type ℓ) → hProp ℓ
∥ X ∥ₚ = ∥ X ∥₁ , squash₁

-- Binary Unions
infix 6 _∪_

_∪_ : ℙ X → ℙ X → ℙ X
A ∪ B = λ x → A x ⊔ B x where
              -- Repeated from Cubical.Functions.Logic
              _⊔_ : hProp ℓ → hProp ℓ → hProp ℓ
              a ⊔ b = ∥ ⟨ a ⟩ ⊎  ⟨ b ⟩ ∥ₚ 

-- When defining union and intersection over families
-- we define an implicit argument X instead of using the module private metavariable
-- since Agda is unable to infer that ℓ-max ℓ X.ℓ = ℓ

-- Indexed Unions
⋃ : {X I : Type ℓ} → (I → ℙ X) → ℙ X
⋃ {I = I} family = λ x → ∥ Σ[ i ∈ I ] (x ∈ family i) ∥ₚ 

-- Indexed Intersections
⋂ : {X I : Type ℓ} → (I → ℙ X) → ℙ X
⋂ {I = I} family = λ x → ∥ (∀ i → (x ∈ family i)) ∥ₚ 

-- Empty subset
∅ : ℙ X
∅ x = ⊥* , isProp⊥*

-- Total subset
𝕋 : ℙ X
𝕋 = λ x → ∥ Lift Unit ∥ₚ 

infixl 7 ～_

～_ : ℙ X → ℙ X
～ A = λ x → x ∉ₚ A

-- The type of inhabited subsets
-- Inspired by the same definition in [martinescardo/TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Powerset.html#3251)

-- A subset A is inhabited if there merely exists an x such that x ∈ A
isInhabited : {X : Type ℓ} → ℙ X → hProp ℓ
isInhabited {X = X} A = ∥ (Σ[ x ∈ X ] x ∈ A) ∥ₚ

ℙ⁺ : Type ℓ → Type (ℓ-suc ℓ)
ℙ⁺ X = Σ[ A ∈ ℙ X ] ⟨ isInhabited A ⟩
