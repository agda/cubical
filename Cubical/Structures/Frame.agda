{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Frame where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP     renaming (SNS-≡ to SNS)
open import Cubical.Structures.Poset
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Family

-- We will adopt the convention of referring using ℓ₀, ℓ₁, ℓ₂ for the
-- carrier level, relation level, and the index type level respectively
private
  variable
    ℓ₀ ℓ₁ ℓ₂ : Level

module JoinSyntax (A : Type ℓ₀) {ℓ₂ : Level} (join : Fam ℓ₂ A → A) where

  join-of : {I : Type ℓ₂} → (I → A) → A
  join-of {I = I} f = join (I , f)

  syntax join-of (λ i → e) = ⋁⟨ i ⟩ e

RawFrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type _
RawFrameStr ℓ₁ ℓ₂ A = PosetStr ℓ₁ A × A × (A → A → A) × (Fam ℓ₂ A → A)

isTop : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → hProp (ℓ-max ℓ₀ ℓ₁)
isTop P x = ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ]) , isPropΠ λ y → snd (y ⊑[ P ] x)

isGLB : (P : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp (ℓ-max ℓ₀ ℓ₁)
isGLB P _∧_ = ∧-GLB , ∧-GLB-prop
  where
    ∧-GLB = -- x ∧ y is a lower bound of {x, y}.
        ((x y    : ∣ P ∣ₚ) → [ (x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y ])
        -- Given any other lower bound z of {x, y}, x ∧ y is _greater_ than that.
      × ((x y z  : ∣ P ∣ₚ) → [ (z ⊑[ P ] x ⊓ z ⊑[ P ] y) ⇒  z ⊑[ P ] (x ∧ y) ])

    ∧-GLB-prop : isProp ∧-GLB
    ∧-GLB-prop =
      isPropΣ
        (isPropΠ2 λ x y → snd ((x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y)) λ _ →
        isPropΠ3 λ x y z → snd (z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] (x ∧ y))

isLUB : (P : Poset ℓ₀ ℓ₁) → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp _
isLUB {ℓ₂ = ℓ₂} P ⋁_ = ⋁-LUB , ⋁-LUB-prop
  where
    ⋁-LUB = ((U : Fam ℓ₂ ∣ P ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ P ] (⋁ U)) ])
          × ((U : Fam ℓ₂ ∣ P ∣ₚ) (x : _) → [ (∀[ y ε U ] (y ⊑[ P ] x)) ⇒ (⋁ U) ⊑[ P ] x ])

    ⋁-LUB-prop : isProp ⋁-LUB
    ⋁-LUB-prop = isPropΣ
                   (λ ψ ϑ → funExt λ U →
                     snd (∀[ y ε U ] (y ⊑[ P ] (⋁ U))) (ψ U) (ϑ U)) λ _ →
                   isPropΠ λ U → isPropΠ λ x →
                     snd (∀[ y ε U ] (y ⊑[ P ] x) ⇒ (⋁ U) ⊑[ P ] x)

isDist : (P : Poset ℓ₀ ℓ₁)
       → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ)
       → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ)
       → hProp _
isDist {ℓ₂ = ℓ₂} P _⊓_ ⋁_ = ∧-dist-over-⋁ , ∧-dist-over-⋁-prop
  where
    open JoinSyntax ∣ P ∣ₚ ⋁_

    ∧-dist-over-⋁ = (x : ∣ P ∣ₚ) (U : Fam ℓ₂ ∣ P ∣ₚ) → x ⊓ (⋁ U) ≡ ⋁⟨ i ⟩ (x ⊓ (U $ i))

    ∧-dist-over-⋁-prop : isProp ∧-dist-over-⋁
    ∧-dist-over-⋁-prop p q = funExt2 λ x U → carrier-is-set P _ _ (p x U) (q x U)
