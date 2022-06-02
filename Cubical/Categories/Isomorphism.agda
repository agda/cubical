{-# OPTIONS --safe #-}
module Cubical.Categories.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Categories.Category
  renaming (CatIso≡ to CatIso≡Ext)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _ {C : Category ℓC ℓC'} where

  open Category C
  open CatIso


  ⋆Iso : {x y z : ob} → (f : CatIso C x y)(g : CatIso C y z) → CatIso C x z
  ⋆Iso f g .mor = f .mor ⋆ g .mor
  ⋆Iso f g .inv = g .inv ⋆ f .inv
  ⋆Iso f g .sec = sym (⋆Assoc _ _ _)
    ∙ (λ i → ⋆Assoc (g .inv) (f .inv) (f .mor) i ⋆ g .mor)
    ∙ (λ i → (g .inv ⋆ f .sec i) ⋆ g .mor)
    ∙ (λ i → ⋆IdR (g .inv) i ⋆ g .mor)
    ∙ g .sec
  ⋆Iso f g .ret = sym (⋆Assoc _ _ _)
    ∙ (λ i → ⋆Assoc (f .mor) (g .mor) (g .inv) i ⋆ f .inv)
    ∙ (λ i → (f .mor ⋆ g .ret i) ⋆ f .inv)
    ∙ (λ i → ⋆IdR (f .mor) i ⋆ f .inv)
    ∙ f .ret

  compIso : {x y z : ob} → (g : CatIso C y z)(f : CatIso C x y) → CatIso C x z
  compIso g f = ⋆Iso f g


  CatIso≡ : {x y : ob} (f g : CatIso C x y) → f .mor ≡ g .mor → f ≡ g
  CatIso≡ f g p = CatIso≡Ext f g p inv≡
    where
    inv≡ : f .inv ≡ g .inv
    inv≡ = sym (⋆IdL _)
      ∙ (λ i → g .sec (~ i) ⋆ f .inv)
      ∙ ⋆Assoc _ _ _
      ∙ (λ i → g .inv ⋆ (p (~ i) ⋆ f .inv))
      ∙ (λ i → g .inv ⋆ f .ret i)
      ∙ ⋆IdR _


  ⋆IsoIdL : {x y : ob} → (f : CatIso C x y) → ⋆Iso idCatIso f ≡ f
  ⋆IsoIdL _ = CatIso≡ _ _ (⋆IdL _)

  ⋆IsoIdR : {x y : ob} → (f : CatIso C x y) → ⋆Iso f idCatIso ≡ f
  ⋆IsoIdR _ = CatIso≡ _ _ (⋆IdR _)


  pathToIso-∙ : {x y z : ob}(p : x ≡ y)(q : y ≡ z) → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q)
  pathToIso-∙ p q = J (λ y p → (z : ob)(q : y ≡ z) → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q))
    (λ _ q → J (λ z q → pathToIso (refl ∙ q) ≡ ⋆Iso (pathToIso refl) (pathToIso q)) pathToIso-∙-refl q) p _ q
    where
    pathToIso-∙-refl : {x : ob} → pathToIso {x = x} (refl ∙ refl) ≡ ⋆Iso (pathToIso refl) (pathToIso refl)
    pathToIso-∙-refl = cong pathToIso (sym compPathRefl)
      ∙ sym (⋆IsoIdL _)
      ∙ (λ i → ⋆Iso (pathToIso-refl (~ i)) (pathToIso refl))


module _ {C : Category ℓC ℓC'} where

  open Category
  open CatIso

  op-Iso : {x y : C .ob} → CatIso C x y → CatIso (C ^op) x y
  op-Iso f .mor = f .inv
  op-Iso f .inv = f .mor
  op-Iso f .sec = f .sec
  op-Iso f .ret = f .ret


module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{F : Functor C D} where

  open Category
  open CatIso
  open Functor


  F-Iso : {x y : C .ob} → CatIso C x y → CatIso D (F .F-ob x) (F .F-ob y)
  F-Iso f .mor = F . F-hom (f .mor)
  F-Iso f .inv = F . F-hom (f .inv)
  F-Iso f .sec = sym (F .F-seq (f .inv) (f .mor)) ∙ cong (F .F-hom) (f .sec) ∙ F .F-id
  F-Iso f .ret = sym (F .F-seq (f .mor) (f .inv)) ∙ cong (F .F-hom) (f .ret) ∙ F .F-id

  F-Iso-PresId : {x : C .ob} → F-Iso (idCatIso {x = x}) ≡ idCatIso
  F-Iso-PresId = CatIso≡ _ _ (F .F-id)

  F-Iso-Pres⋆ : {x y z : C .ob} → (f : CatIso C x y)(g : CatIso C y z) → F-Iso (⋆Iso f g) ≡ ⋆Iso (F-Iso f) (F-Iso g)
  F-Iso-Pres⋆ _ _ = CatIso≡ _ _ (F .F-seq _ _)
