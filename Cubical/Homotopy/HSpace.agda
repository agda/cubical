{-# OPTIONS --safe #-}
module Cubical.Homotopy.HSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.HITs.S1
open import Cubical.HITs.Sn

record HSpace {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  constructor HSp
  field
    μ : typ A → typ A → typ A
    μₗ : (x : typ A) → μ (pt A) x ≡ x
    μᵣ : (x : typ A) → μ x (pt A) ≡ x
    μₗᵣ : μₗ (pt A) ≡ μᵣ (pt A)

record AssocHSpace {ℓ : Level} {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor AssocHSp
  field
    μ-assoc : (x y z : _)
      → HSpace.μ e (HSpace.μ e x y) z ≡ HSpace.μ e x (HSpace.μ e y z)

    μ-assoc-filler : (y z : typ A)
      → PathP (λ i → HSpace.μ e (HSpace.μₗ e y i) z
                    ≡ HSpace.μₗ e (HSpace.μ e y z) i)
               (μ-assoc (pt A) y z)
               refl

-- Instances
open HSpace
open AssocHSpace

-- S¹
S1-HSpace : HSpace (S₊∙ 1)
μ S1-HSpace = _·_
μₗ S1-HSpace x = refl
μᵣ S1-HSpace base = refl
μᵣ S1-HSpace (loop i) = refl
μₗᵣ S1-HSpace x = refl

S1-AssocHSpace : AssocHSpace S1-HSpace
μ-assoc S1-AssocHSpace base _ _ = refl
μ-assoc S1-AssocHSpace (loop i) x y j = h x y j i
  where
  h : (x y : S₊ 1) → cong (_· y) (rotLoop x) ≡ rotLoop (x · y)
  h = wedgeconFun _ _ (λ _ _ → isOfHLevelPath 2 (isGroupoidS¹ _ _) _ _)
        (λ x → refl)
        (λ { base → refl ; (loop i) → refl})
        refl
μ-assoc-filler S1-AssocHSpace _ _ = refl
