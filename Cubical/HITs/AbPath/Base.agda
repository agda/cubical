module Cubical.HITs.AbPath.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

-- 'Abelianised' path types (useful for encode-decode computations of π₁ᵃᵇ)
data _≡ᵃᵇ_ {ℓ} {A : Type ℓ} (x y : A) : Type ℓ
  where
  paths : x ≡ y → x ≡ᵃᵇ y
  com : (p q r : x ≡ y) → paths (p ∙ sym q ∙ r) ≡ paths (r ∙ sym q ∙ p)

Pathᵃᵇ : ∀ {ℓ} (A : Type ℓ) (x y : A) → Type ℓ
Pathᵃᵇ A = _≡ᵃᵇ_

Ωᵃᵇ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
Ωᵃᵇ (A , a) = a ≡ᵃᵇ a
