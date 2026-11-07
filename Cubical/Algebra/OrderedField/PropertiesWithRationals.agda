module Cubical.Algebra.OrderedField.PropertiesWithRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.OrderedCommRing.Morphisms
open import Cubical.Algebra.OrderedField
open import Cubical.Algebra.OrderedField.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base  as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level

module ℚ↪Theory (F : OrderedField ℓ ℓ') ((ι , ιOFHom) : OrderedFieldHom ℚOrderedField F)
  where

  open OrderedFieldStr (snd F)
  open OrderedFieldReasoning F
  open RingTheory (OrderedField→Ring F)
  open IsOrderedFieldHom ιOFHom

  private
    reflect≤ = isOrderedCommRingMono→reflect≤ isOrderedCommRingMono

  ι₀₊ : Σ ℚ (0 ≤ℚ_) → ⟨ F ⟩
  ι₀₊ = ι ∘ fst

  ι₊ : Σ ℚ (0 <ℚ_) → ⟨ F ⟩
  ι₊ = ι ∘ fst

  module ℚ↪Reasoning where

    _<·ι[_] : ∀ {x y} z → x < y → x · ι₊ z < y · ι₊ z
    _<·ι[_] z = _<·[ _ , subst (_< _) pres0 (pres< _ _ (snd z)) ]

    ι[_]·<_ : ∀ {x y} z → x < y → ι₊ z · x < ι₊ z · y
    ι[_]·<_ z = [ _ , subst (_< _) pres0 (pres< _ _ (snd z)) ]·<_

    _≤·ι[_] : ∀ {x y} z → x ≤ y → x · ι₀₊ z ≤ y · ι₀₊ z
    _≤·ι[_] z = _≤·[ _ , subst (_≤ _) pres0 (pres≤ _ _ (snd z)) ]

    ι[_]·≤_ : ∀ {x y} z → x ≤ y → ι₀₊ z · x ≤ ι₀₊ z · y
    ι[_]·≤_ z = [ _ , subst (_≤ _) pres0 (pres≤ _ _ (snd z)) ]·≤_

  ι0· : ∀ x → ι 0 · x ≡ 0f
  ι0· x = congL _·_ pres0 ∙ 0LeftAnnihilates x

  ι1· : ∀ x → ι 1 · x ≡ x
  ι1· x = congL _·_ pres1 ∙ ·IdL x

  0<ι₊ : ∀ a → 0f < ι₊ a
  0<ι₊ = subst (_< ι _) pres0 ∘ uncurry (pres< 0)

  0<ι→0< : ∀ a → 0f < ι a → 0 <ℚ a
  0<ι→0< a = ℚ.recompute< ∘ reflect< _ _ ∘ subst (_< ι a) (sym pres0)

  0≤ι₊ : ∀ a → 0f ≤ ι₊ a
  0≤ι₊ = <-≤-weaken 0f _ ∘ 0<ι₊

  0≤ι₀₊ : ∀ a → 0f ≤ ι₀₊ a
  0≤ι₀₊ = subst (_≤ ι _) pres0 ∘ uncurry (pres≤ 0)

  0≤ι→0≤ : ∀ a → 0f ≤ ι a → 0 ≤ℚ a
  0≤ι→0≤ a = ℚ.recompute≤ ∘ reflect≤ _ _ ∘ subst (_≤ ι a) (sym pres0)

  isArchimedean : Type (ℓ-max ℓ ℓ')
  isArchimedean = ∀ x y → x < y → ∃[ q ∈ ℚ ] (x < ι q) × (ι q < y)

  isPropIsArchimedean : isProp isArchimedean
  isPropIsArchimedean = isPropΠ3 λ _ _ _ → squash₁

open ℚ↪Theory public using (module ℚ↪Reasoning)
