{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Field where
{-
  Definition of a field following
  Mines, Richman and Ruitenburg, "A Course in Constructive Algebra" (1988)

  A field is a commutative ring such that nonzero elements have to be invertible,
  where "nonzero" is not neccessarily based on the equality of the underlying
  type of the ring.
  NOTE that the zero ring is not excluded by this definition.
-}

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic using ([_])
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_; isProp¬)

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)

open import Cubical.Structures.CommRing
import Cubical.Structures.Ring

private
  variable
    ℓ : Level

{- This is the obvious example of an inequality relation -}
denialInequality : (R : CommRing {ℓ}) → ⟨ R ⟩ → ⟨ R ⟩ → hProp _
denialInequality _ x y = (¬ x ≡ y) , isProp¬ (x ≡ y)

module _ (R : CommRing {ℓ}) (inequality : ⟨ R ⟩ → ⟨ R ⟩ → hProp ℓ) where
  open commring-·syntax R
  open commRingAxioms R
  open Cubical.Structures.Ring.calculations (CommRing→Ring R)

  nonZeroElementsAreInvertible : Type ℓ
  nonZeroElementsAreInvertible = ((x : ⟨ R ⟩) → [ inequality x ₀ ] → Σ[ y ∈ ⟨ R ⟩ ] (x · y) ≡ ₁)


  isPropNonZeroElementsInvertible : isProp (nonZeroElementsAreInvertible)
  isPropNonZeroElementsInvertible witness1 witness2 i x x-non-zero =
    let
      y₁ = fst (witness1 x x-non-zero)
      y₁-inv = snd (witness1 x x-non-zero)
      y₂ = fst (witness2 x x-non-zero)
      y₂-inv = snd (witness2 x x-non-zero)

      y₁-y₂divides0 = ₀                        ≡⟨ sym (commring+-rinv ₁) ⟩
                      ₁ - ₁                    ≡⟨ cong (λ u → u - ₁) (sym (y₁-inv)) ⟩
                      (x · y₁) - ₁             ≡⟨ cong (λ u → (x · y₁) - u) (sym (y₂-inv)) ⟩
                      (x · y₁) - (x · y₂)      ≡⟨ cong (λ u → (x · y₁) + u)
                                                       (sym (-commutesWithRight-· x y₂)) ⟩
                      (x · y₁) + (x · (- y₂))  ≡⟨ sym (commring-rdist _ _ _) ⟩
                      x · (y₁ - y₂)            ∎

      y₁-y₂≡0 = y₁ - y₂                ≡⟨ sym (commring·-lid _) ⟩
                ₁ · (y₁ - y₂)          ≡⟨ cong (λ u → u · (y₁ - y₂)) (sym y₁-inv) ⟩
                (x · y₁) · (y₁ - y₂)   ≡⟨ cong (λ u → u · (y₁ - y₂)) (commring-comm R _ _) ⟩
                (y₁ · x) · (y₁ - y₂)   ≡⟨ sym (commring·-assoc _ _ _) ⟩
                y₁ · (x · (y₁ - y₂))   ≡⟨ cong (λ u → y₁ · u) (sym y₁-y₂divides0) ⟩
                y₁ · ₀                 ≡⟨ 0-rightNullifies _ ⟩
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
