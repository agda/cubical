{-# OPTIONS --safe #-}
module Cubical.Categories.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _ {C : Category ℓC ℓC'} where

  open Category C
  open isIso


  ⋆Iso : {x y z : ob} → (f : CatIso C x y)(g : CatIso C y z) → CatIso C x z
  ⋆Iso f g .fst = f .fst ⋆ g .fst
  ⋆Iso f g .snd .inv = g .snd .inv ⋆ f .snd .inv
  ⋆Iso f g .snd .sec = sym (⋆Assoc _ _ _)
    ∙ (λ i → ⋆Assoc (g .snd .inv) (f .snd .inv) (f .fst) i ⋆ g .fst)
    ∙ (λ i → (g .snd .inv ⋆ f .snd .sec i) ⋆ g .fst)
    ∙ (λ i → ⋆IdR (g .snd .inv) i ⋆ g .fst)
    ∙ g .snd .sec
  ⋆Iso f g .snd .ret = sym (⋆Assoc _ _ _)
    ∙ (λ i → ⋆Assoc (f .fst) (g .fst) (g .snd .inv) i ⋆ f .snd .inv)
    ∙ (λ i → (f .fst ⋆ g .snd .ret i) ⋆ f .snd .inv)
    ∙ (λ i → ⋆IdR (f .fst) i ⋆ f .snd .inv)
    ∙ f .snd .ret

  compIso : {x y z : ob} → (g : CatIso C y z)(f : CatIso C x y) → CatIso C x z
  compIso g f = ⋆Iso f g


  ⋆IsoIdL : {x y : ob} → (f : CatIso C x y) → ⋆Iso idCatIso f ≡ f
  ⋆IsoIdL _ = CatIso≡ _ _ (⋆IdL _)

  ⋆IsoIdR : {x y : ob} → (f : CatIso C x y) → ⋆Iso f idCatIso ≡ f
  ⋆IsoIdR _ = CatIso≡ _ _ (⋆IdR _)


  pathToIso-∙ : {x y z : ob}(p : x ≡ y)(q : y ≡ z) → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q)
  pathToIso-∙ p q = J2 (λ y p z q → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q)) pathToIso-∙-refl p q
    where
    pathToIso-∙-refl : {x : ob} → pathToIso {x = x} (refl ∙ refl) ≡ ⋆Iso (pathToIso refl) (pathToIso refl)
    pathToIso-∙-refl = cong pathToIso (sym compPathRefl)
      ∙ sym (⋆IsoIdL _)
      ∙ (λ i → ⋆Iso (pathToIso-refl (~ i)) (pathToIso refl))


  pathToIso-Comm : {x y z w : ob}
    → (p : x ≡ y)(q : z ≡ w)
    → (f : Hom[ x , z ])(g : Hom[ y , w ])
    → PathP (λ i → Hom[ p i , q i ]) f g
    → f ⋆ pathToIso {C = C} q .fst ≡ pathToIso {C = C} p .fst ⋆ g
  pathToIso-Comm {x = x} {z = z} p q =
    J2 (λ y p w q →
        (f : Hom[ x , z ])(g : Hom[ y , w ])
      → PathP (λ i → Hom[ p i , q i ]) f g
      → f ⋆ pathToIso {C = C} q .fst ≡ pathToIso {C = C} p .fst ⋆ g)
    sqr-refl p q
    where
    sqr-refl : (f g : Hom[ x , z ]) → f ≡ g
      → f ⋆ pathToIso {C = C} refl .fst ≡ pathToIso {C = C} refl .fst ⋆ g
    sqr-refl f g p = (λ i → f ⋆ pathToIso-refl {C = C} i .fst)
      ∙ ⋆IdR _ ∙ p ∙ sym (⋆IdL _)
      ∙ (λ i → pathToIso-refl {C = C} (~ i) .fst ⋆ g)

  pathToIso-Square : {x y z w : ob}
    → (p : x ≡ y)(q : z ≡ w)
    → (f : Hom[ x , z ])(g : Hom[ y , w ])
    → f ⋆ pathToIso {C = C} q .fst ≡ pathToIso {C = C} p .fst ⋆ g
    → PathP (λ i → Hom[ p i , q i ]) f g
  pathToIso-Square {x = x} {z = z} p q =
    J2 (λ y p w q →
        (f : Hom[ x , z ])(g : Hom[ y , w ])
      → f ⋆ pathToIso {C = C} q .fst ≡ pathToIso {C = C} p .fst ⋆ g
      → PathP (λ i → Hom[ p i , q i ]) f g)
    sqr-refl p q
    where
    sqr-refl : (f g : Hom[ x , z ])
      → f ⋆ pathToIso {C = C} refl .fst ≡ pathToIso {C = C} refl .fst ⋆ g
      → f ≡ g
    sqr-refl f g p = sym (⋆IdR _)
      ∙ (λ i → f ⋆ pathToIso-refl {C = C} (~ i) .fst)
      ∙ p
      ∙ (λ i → pathToIso-refl {C = C} i .fst ⋆ g)
      ∙ ⋆IdL _

  module _ (isUnivC : isUnivalent C) where

    open isUnivalent isUnivC

    isoToPath-Square : {x y z w : ob}
      → (p : CatIso C x y)(q : CatIso C z w)
      → (f : Hom[ x , z ])(g : Hom[ y , w ])
      → f ⋆ q .fst ≡ p .fst ⋆ g
      → PathP (λ i → Hom[ CatIsoToPath p i , CatIsoToPath q i ]) f g
    isoToPath-Square p q f g comm =
      pathToIso-Square (CatIsoToPath p) (CatIsoToPath q) _ _
        ((λ i → f ⋆ secEq (univEquiv _ _) q i .fst) ∙ comm ∙ (λ i → secEq (univEquiv _ _) p (~ i) .fst ⋆ g))


module _ {C : Category ℓC ℓC'} where

  open Category
  open isIso

  op-Iso : {x y : C .ob} → CatIso C x y → CatIso (C ^op) x y
  op-Iso f .fst = f .snd .inv
  op-Iso f .snd .inv = f .fst
  op-Iso f .snd .sec = f .snd .sec
  op-Iso f .snd .ret = f .snd .ret


module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{F : Functor C D} where

  open Category hiding (_∘_)
  open isIso
  open Functor


  F-PresIsIso : {x y : C .ob}{f : C [ x , y ]} → isIso C f → isIso D (F .F-hom f)
  F-PresIsIso f .inv = F . F-hom (f .inv)
  F-PresIsIso f .sec = sym (F .F-seq (f .inv) _) ∙ cong (F .F-hom) (f .sec) ∙ F .F-id
  F-PresIsIso f .ret = sym (F .F-seq _ (f .inv)) ∙ cong (F .F-hom) (f .ret) ∙ F .F-id


  F-Iso : {x y : C .ob} → CatIso C x y → CatIso D (F .F-ob x) (F .F-ob y)
  F-Iso f .fst = F . F-hom (f .fst)
  F-Iso f .snd = F-PresIsIso (f .snd)

  F-Iso-PresId : {x : C .ob} → F-Iso (idCatIso {x = x}) ≡ idCatIso
  F-Iso-PresId = CatIso≡ _ _ (F .F-id)

  F-Iso-Pres⋆ : {x y z : C .ob} → (f : CatIso C x y)(g : CatIso C y z) → F-Iso (⋆Iso f g) ≡ ⋆Iso (F-Iso f) (F-Iso g)
  F-Iso-Pres⋆ _ _ = CatIso≡ _ _ (F .F-seq _ _)


  F-pathToIso : {x y : C .ob} → (p : x ≡ y) → F-Iso (pathToIso p) ≡ pathToIso (cong (F .F-ob) p)
  F-pathToIso p = J (λ y p → F-Iso (pathToIso p) ≡ pathToIso (cong (F .F-ob) p)) F-pathToIso-refl p
    where
    F-pathToIso-refl : {x : C .ob} → F-Iso (pathToIso {x = x} refl) ≡ pathToIso (cong (F .F-ob) refl)
    F-pathToIso-refl = cong F-Iso pathToIso-refl
      ∙ F-Iso-PresId
      ∙ sym pathToIso-refl

  F-pathToIso-∘ : {x y : C .ob} → F-Iso ∘ pathToIso {x = x} {y = y} ≡ pathToIso ∘ cong (F .F-ob)
  F-pathToIso-∘ i p = F-pathToIso p i
