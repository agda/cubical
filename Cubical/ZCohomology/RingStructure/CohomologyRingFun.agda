{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CohomologyRingFun where

{-
   There is two definitionof the Cohomology Ring.
   We recommend to use the HIT definition (the other one)
   as the ring product is eaiser to handle.
   Nevertheless the equality is harder to handle so
   this definition can interessting too.
-}

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.DirectSumFun

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

private variable
  ℓ ℓ' : Level

open PlusBis

module _ (A : Type ℓ) where

  H*FunR : Ring ℓ
  H*FunR = ⊕FunGradedRing-Ring
           _+'_ (makeIsMonoid isSetℕ +'-assoc +'-rid +'-lid)
           +'≡+
           (λ k → coHom k A)
           (λ k → snd (coHomGroup k A))
           1⌣
           _⌣_
           (λ {k} {l} → 0ₕ-⌣ k l)
           (λ {k} {l} → ⌣-0ₕ k l)
           (λ _ _ _ → sym (ΣPathTransport→PathΣ _ _ ((sym (+'-assoc _ _ _)) , (sym (assoc-⌣ _ _ _ _ _ _)))))
           (λ _ → sym (ΣPathTransport→PathΣ _ _ (sym (+'-rid _) , sym (lUnit⌣ _ _))))
           (λ _ → ΣPathTransport→PathΣ _ _ (refl , transportRefl _ ∙ rUnit⌣ _ _))
           (λ _ _ _ → leftDistr-⌣ _ _ _ _ _)
           λ _ _ _ → rightDistr-⌣ _ _ _ _ _

  H*Fun : Type ℓ
  H*Fun = fst H*FunR
