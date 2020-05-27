{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.DenialField where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Data.Empty
open import Cubical.Structures.CommRing
import Cubical.Structures.Ring

private
  variable
    ℓ : Level

module _ (R : CommRing {ℓ}) where
  open commring-·syntax R
  open commRingAxioms R
  open Cubical.Structures.Ring.calculations (CommRing→Ring R)

  isDenialField : Type ℓ
  isDenialField = (x : ⟨ R ⟩) → (x ≡ ₀ → ⊥) → Σ[ y ∈ ⟨ R ⟩ ] (x · y) ≡ ₁

  isPropIsField : isProp (isDenialField)
  isPropIsField witness1 witness2 i x x-non-zero =
    let
      y₁ = fst (witness1 x x-non-zero)
      y₁-inv = snd (witness1 x x-non-zero)
      y₂ = fst (witness2 x x-non-zero)
      y₂-inv = snd (witness2 x x-non-zero)

      y₁-y₂divides0 = ₀                        ≡⟨ sym (commring+-rinv ₁) ⟩
                      ₁ - ₁                    ≡⟨ cong (λ u → u - ₁) (sym (y₁-inv)) ⟩
                      (x · y₁) - ₁             ≡⟨ cong (λ u → (x · y₁) - u) (sym (y₂-inv)) ⟩
                      (x · y₁) - (x · y₂)      ≡⟨ cong (λ u → (x · y₁) + u) (sym (-commutesWithRight-· x y₂)) ⟩
                      (x · y₁) + (x · (- y₂))  ≡⟨ sym (commring-rdist _ _ _) ⟩
                      x · (y₁ - y₂)            ∎

      y₁-y₂≡0 = y₁ - y₂                ≡⟨ sym (commring·-lid _) ⟩
                ₁ · (y₁ - y₂)          ≡⟨ cong (λ u → u · (y₁ - y₂)) (sym y₁-inv) ⟩
                (x · y₁) · (y₁ - y₂)   ≡⟨ cong (λ u → u · (y₁ - y₂)) (commring-comm R _ _) ⟩
                (y₁ · x) · (y₁ - y₂)   ≡⟨ sym (commring·-assoc _ _ _) ⟩
                y₁ · (x · (y₁ - y₂))   ≡⟨ cong (λ u → y₁ · u) (sym y₁-y₂divides0) ⟩
                y₁ · ₀                 ≡⟨ sym (0-rightNullifies _ ) ⟩
                ₀                      ∎

      inverseIsUnique = y₁                ≡⟨ sym (commring+-rid _) ⟩
                        y₁ + ₀            ≡⟨ cong (λ u → y₁ + u) (sym (commring+-linv _)) ⟩
                        y₁ + (- y₂ + y₂)  ≡⟨ commring+-assoc _ _ _ ⟩
                        (y₁ - y₂) + y₂    ≡⟨ cong (λ u → u + y₂) y₁-y₂≡0 ⟩
                        ₀ + y₂            ≡⟨ commring+-lid _ ⟩
                        y₂                ∎

    in ΣProp≡ (λ y → commRingIsSet R (x · y) ₁)
              {witness1 x x-non-zero}
              {witness2 x x-non-zero}
              inverseIsUnique
              i
