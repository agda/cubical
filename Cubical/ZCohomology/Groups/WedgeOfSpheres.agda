{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.Groups.WedgeOfSpheres where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Groups.Wedge

open import Cubical.HITs.Sn
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Susp
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; ∣_∣ to ∣_∣₋₁)
open import Cubical.HITs.Nullification
open import Cubical.Data.Int
open import Cubical.Data.Prod
open import Cubical.HITs.Truncation renaming (elim to trElim)
open import Cubical.Data.Group.Base renaming (Iso to grIso ; compIso to compGrIso ; invIso to invGrIso ; idIso to idGrIso)

S¹⋁S¹ : Type₀
S¹⋁S¹ = S₊∙ 1 ⋁ S₊∙ 1

S²⋁S¹⋁S¹ : Type₀
S²⋁S¹⋁S¹ = S₊∙ 2 ⋁ (S¹⋁S¹ , inl north)

------------- H⁰(S¹⋁S¹) ------------
H⁰-S¹⋁S¹ : grIso (coHomGr 0 S¹⋁S¹) intGroup
H⁰-S¹⋁S¹ =
  Iso'→Iso
    (iso'
      (iso
        (sRec isSetInt (λ f → f (inl north)))
        (λ a → ∣ (λ _ → a) ∣₂)
        (λ _ → refl)
        (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
               (λ f → cong ∣_∣₂
                           (funExt (PushoutToProp
                                      (λ _ → isSetInt _ _)
                                      (suspToPropRec north (λ _ → isSetInt _ _) refl)
                                      (suspToPropRec north (λ _ → isSetInt _ _) λ i → f (push tt i)))))))
      (sElim2 (λ _ _ → isOfHLevelPath 2 isSetInt _ _) λ a b → addLemma (a (inl north)) (b (inl north))))

------------- H¹(S¹⋁S¹) ------------
H¹-S¹⋁S¹ : grIso (coHomGr 1 S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S¹⋁S¹ = compGrIso (Hⁿ-⋁ 0)
                     (dirProdIso (invGrIso H¹-S¹≅ℤ) (invGrIso H¹-S¹≅ℤ))

------------- H⁰(S²⋁S¹⋁S¹) ---------
H⁰-S²⋁S¹⋁S¹ : grIso (coHomGr 0 S²⋁S¹⋁S¹) intGroup
H⁰-S²⋁S¹⋁S¹ =
  invGrIso
    (Iso'→Iso
      (iso'
        (iso
          (λ a →  ∣ (λ _ → a) ∣₂)
          (sRec isSetInt (λ f → f (inl north)))
          (sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                 λ a → cong ∣_∣₂ (funExt (PushoutToProp (λ _ → isSetInt _ _)
                                           (suspToPropRec north (λ _ → isSetInt _ _) refl)
                                           (PushoutToProp (λ _ → isSetInt _ _)
                                             (suspToPropRec north (λ _ → isSetInt _ _) (cong a (push tt)))
                                             (suspToPropRec north (λ _ → isSetInt _ _) (cong a (push tt ∙ λ i → inr (push tt i))))))))
          (λ _ → refl))
        λ a b → cong ∣_∣₂ (funExt λ _ → sym (addLemma a b))))

------------- H¹(S²⋁S¹⋁S¹) ---------
H¹-S²⋁S¹⋁S¹ : grIso (coHomGr 1 S²⋁S¹⋁S¹) (dirProd intGroup intGroup)
H¹-S²⋁S¹⋁S¹ = compGrIso (Hⁿ-⋁ 0)
                 (compGrIso
                    (dirProdIso H¹-S²≅0 H¹-S¹⋁S¹)
                    lUnitGroupIso)

------------- H²(S²⋁S¹⋁S¹) ---------
H²-S²⋁S¹⋁S¹ : grIso (coHomGr 2 S²⋁S¹⋁S¹) intGroup
H²-S²⋁S¹⋁S¹ = compGrIso (Hⁿ-⋁ 1)
                (compGrIso (dirProdIso (invGrIso (Hⁿ-Sⁿ≅ℤ 1))
                           (Hⁿ-⋁ 1))
                   (compGrIso (dirProdIso (idGrIso _)
                                (compGrIso (dirProdIso H²-S¹≅0 H²-S¹≅0) lUnitGroupIso))
                              rUnitGroupIso))
