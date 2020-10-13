{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.HITs.Pushout

--- This module contains a proof that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B), n ≥ 1

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where
  module I = MV (typ A) (typ B) Unit (λ _ → pt A) (λ _ → pt B)

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  Hⁿ-⋁ zero = BijectionIsoToGroupIso bijIso
    where
    surj-helper : (x : coHom 0 Unit) → isInIm _ _ (I.Δ 0) x
    surj-helper =
      sElim (λ _ → isOfHLevelSuc 1 propTruncIsProp)
            λ f → ∣ (∣ (λ _ → f tt) ∣₂ , 0ₕ 0) , cong ∣_∣₂ (funExt λ _ → -rUnitₖ 0 (f tt)) ∣₁

    helper : (x : coHom 1 (A ⋁ B)) → isInIm _ _ (I.d 0) x → x ≡ 0ₕ 1
    helper x inim =
      pRec (setTruncIsSet _ _)
           (λ p → sym (snd p) ∙
                       MV.Im-Δ⊂Ker-d _ _ Unit (λ _ → pt A) (λ _ → pt B) 0 (fst p) (surj-helper (fst p)))
             inim

    bijIso : BijectionIso (coHomGr 1 (A ⋁ B)) (×coHomGr 1 (typ A) (typ B))
    BijectionIso.map' bijIso = I.i 1
    BijectionIso.inj bijIso =
      sElim (λ _ → isSetΠ λ _ → isProp→isSet (setTruncIsSet _ _))
            λ f inker → helper ∣ f ∣₂ (I.Ker-i⊂Im-d 0 ∣ f ∣₂ inker)
    BijectionIso.surj bijIso p = I.Ker-Δ⊂Im-i 1 p (isContr→isProp (isContrHⁿ-Unit 0) _ _)

  Hⁿ-⋁ (suc n) =
    vSES→GroupIso _ _
      (ses (isOfHLevelSuc 0 (isContrHⁿ-Unit n))
           (isOfHLevelSuc 0 (isContrHⁿ-Unit (suc n)))
           (I.d (suc n))
           (I.Δ (suc (suc n)))
           (I.i (suc (suc n)))
           (I.Ker-i⊂Im-d (suc n))
           (I.Ker-Δ⊂Im-i (suc (suc n))))

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥) → ((x : typ B) → ∥ pt B ≡ x ∥) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥
  wedgeConnected conA conB =
    PushoutToProp (λ _ → propTruncIsProp)
                  (λ a → pRec propTruncIsProp (λ p → ∣ cong inl p ∣₁) (conA a))
                   λ b → pRec propTruncIsProp (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b)
