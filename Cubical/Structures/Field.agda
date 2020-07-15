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
  open comm-ring-syntax R
  open comm-ring-axioms R
  open Cubical.Structures.Ring.theory (CommRing→Ring R)

  nonZeroElementsAreInvertible : Type ℓ
  nonZeroElementsAreInvertible = ((x : ⟨ R ⟩) → [ inequality x 0r ] → Σ[ y ∈ ⟨ R ⟩ ] (x · y) ≡ 1r)


  isPropNonZeroElementsInvertible : isProp (nonZeroElementsAreInvertible)
  isPropNonZeroElementsInvertible witness1 witness2 i x x-non-zero =
    let
      y1r = fst (witness1 x x-non-zero)
      y1r-inv = snd (witness1 x x-non-zero)
      y₂ = fst (witness2 x x-non-zero)
      y₂-inv = snd (witness2 x x-non-zero)

      y1r-y₂divides0 = 0r                        ≡⟨ sym (commring+-rinv 1r) ⟩
                      1r - 1r                    ≡⟨ cong (λ u → u - 1r) (sym (y1r-inv)) ⟩
                      (x · y1r) - 1r             ≡⟨ cong (λ u → (x · y1r) - u) (sym (y₂-inv)) ⟩
                      (x · y1r) - (x · y₂)      ≡⟨ cong (λ u → (x · y1r) + u)
                                                       (sym (-commutesWithRight-· x y₂)) ⟩
                      (x · y1r) + (x · (- y₂))  ≡⟨ sym (commring-rdist _ _ _) ⟩
                      x · (y1r - y₂)            ∎

      y1r-y₂≡0 = y1r - y₂                ≡⟨ sym (commring·-lid _) ⟩
                1r · (y1r - y₂)          ≡⟨ cong (λ u → u · (y1r - y₂)) (sym y1r-inv) ⟩
                (x · y1r) · (y1r - y₂)   ≡⟨ cong (λ u → u · (y1r - y₂)) (commring-comm R _ _) ⟩
                (y1r · x) · (y1r - y₂)   ≡⟨ sym (commring·-assoc _ _ _) ⟩
                y1r · (x · (y1r - y₂))   ≡⟨ cong (λ u → y1r · u) (sym y1r-y₂divides0) ⟩
                y1r · 0r                 ≡⟨ 0-rightNullifies _ ⟩
                0r                      ∎

      inverseIsUnique = y1r                ≡⟨ sym (commring+-rid _) ⟩
                        y1r + 0r            ≡⟨ cong (λ u → y1r + u) (sym (commring+-linv _)) ⟩
                        y1r + (- y₂ + y₂)  ≡⟨ commring+-assoc _ _ _ ⟩
                        (y1r - y₂) + y₂    ≡⟨ cong (λ u → u + y₂) y1r-y₂≡0 ⟩
                        0r + y₂            ≡⟨ commring+-lid _ ⟩
                        y₂                ∎

    in Σ≡Prop (λ y → commRingIsSet R (x · y) 1r)
              {witness1 x x-non-zero}
              {witness2 x x-non-zero}
              inverseIsUnique
              i
