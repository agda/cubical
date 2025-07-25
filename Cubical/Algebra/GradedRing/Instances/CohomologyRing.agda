{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.GradedRing.Instances.CohomologyRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.NatPlusBis
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.GradedRing.Base
open import Cubical.Algebra.GradedRing.DirectSumHIT

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

private variable
  ℓ : Level

open PlusBis
open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆

module _
  (A : Type ℓ)
  where

  CohomologyRing-GradedRing : GradedRing ℓ-zero ℓ
  CohomologyRing-GradedRing = makeGradedRingSelf
                              NatPlusBis-Monoid
                              (λ k → coHom k A)
                              (λ k → snd (coHomGroup k A) )
                              1⌣
                              _⌣_
                              (λ {k} {l} → 0ₕ-⌣ k l)
                              (λ {k} {l} → ⌣-0ₕ k l)
                              (λ _ _ _ → sym (ΣPathTransport→PathΣ _ _ ((sym (+'-assoc _ _ _)) , (sym (assoc-⌣ _ _ _ _ _ _)))) )
                              (λ _ → sym (ΣPathTransport→PathΣ _ _ (sym (+'-rid _) , sym (lUnit⌣ _ _))))
                              (λ _ → ΣPathTransport→PathΣ _ _ (refl , transportRefl _ ∙ rUnit⌣ _ _))
                              (λ _ _ _ → leftDistr-⌣ _ _ _ _ _)
                              ( λ _ _ _ → rightDistr-⌣ _ _ _ _ _)
