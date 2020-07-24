{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.SigmaFrame where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Structures.Poset
open import Cubical.Data.Sigma
open import Cubical.Foundations.Logic
open import Cubical.Data.Nat
open import Cubical.Functions.FunExtEquiv    using (funExt₂)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level

-- Some pretty syntax for writing down sup operators.

module JoinSyntax (A : Type ℓ₀) (join : (ℕ → A) → A) where

  join-syntax : (ℕ → A) → A
  join-syntax f = join f

  syntax join-syntax (λ i → e) = ⋁⟨ i ⟩ e

RawσFrameStr : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
RawσFrameStr ℓ₁ A = PosetStr ℓ₁ A × A × (A → A → A) × ((ℕ → A) → A)

isTop : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → hProp (ℓ-max ℓ₀ ℓ₁)
isTop P x = ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ]) , isPropΠ λ y → isProp[] (y ⊑[ P ] x)

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
        (isPropΠ2 λ x y → isProp[] ((x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y)) λ _ →
        isPropΠ3 λ x y z → isProp[] (z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] (x ∧ y))

isLUB : (P : Poset ℓ₀ ℓ₁) → ((ℕ → ∣ P ∣ₚ) → ∣ P ∣ₚ) → hProp (ℓ-max ℓ₀ ℓ₁)
isLUB P ⋁_ = ⋁-LUB , ⋁-LUB-prop
  where
    ⋁-LUB =
        ((U : ℕ → ∣ P ∣ₚ) → (i : ℕ) → [ (U i) ⊑[ P ] (⋁ U) ])
      × ((U : ℕ → ∣ P ∣ₚ) (x : ∣ P ∣ₚ) → ((i : ℕ) → [ (U i) ⊑[ P ] x ]) → [ (⋁ U) ⊑[ P ] x ])

    ⋁-LUB-prop : isProp ⋁-LUB
    ⋁-LUB-prop =
      isPropΣ
        (isPropΠ2 (λ U i → isProp[] ((U i) ⊑[ P  ] (⋁ U)))) λ _ →
        isPropΠ2 λ U x → isPropΠ λ i → isProp[] ((⋁ U) ⊑[ P ] x)

isDist : (P : Poset ℓ₀ ℓ₁)
       → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ)
       → ((ℕ → ∣ P ∣ₚ) → ∣ P ∣ₚ)
       → hProp ℓ₀
isDist P _∧_ ⋁_ = ∧-dist-over-⋁ , ∧-dist-over-⋁-prop
  where
    open JoinSyntax ∣ P ∣ₚ ⋁_

    ∧-dist-over-⋁ =
      (x : ∣ P ∣ₚ) (U : ℕ → ∣ P ∣ₚ) → x ∧ (⋁ U) ≡ ⋁⟨ i ⟩ (x ∧ (U i))

    ∧-dist-over-⋁-prop : isProp ∧-dist-over-⋁
    ∧-dist-over-⋁-prop p q = funExt₂ λ x U → carrier-is-set P _ _ (p x U) (q x U)

σFrameAx : {A : Type ℓ₀} → RawσFrameStr ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
σFrameAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = A} (s@(_⊑_ , _) , ⊤ , _∧_ , ⋁_) =
  isTop P ⊤ ⊓ isGLB P _∧_ ⊓ isLUB P ⋁_ ⊓ isDist P _∧_ ⋁_
  where
    P : Poset ℓ₀ ℓ₁
    P = A , s

σFrameStr : (ℓ₁ : Level) → Type ℓ₀ → Type _
σFrameStr ℓ₁ A = Σ[ s ∈ RawσFrameStr ℓ₁ A ] [ σFrameAx s ]

σFrame : (ℓ₀ ℓ₁ : Level) → Type _
σFrame ℓ₀ ℓ₁ = TypeWithStr ℓ₀ (σFrameStr ℓ₁)
