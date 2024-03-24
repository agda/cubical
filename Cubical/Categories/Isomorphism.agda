{-# OPTIONS --safe #-}
module Cubical.Categories.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism hiding (invIso ; compIso ; isIso)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _ {C : Category ℓC ℓC'} where

  open Category C
  open isIso


  invIso : {x y : ob} → CatIso C x y → CatIso C y x
  invIso f .fst = f .snd .inv
  invIso f .snd .inv = f .fst
  invIso f .snd .sec = f .snd .ret
  invIso f .snd .ret = f .snd .sec

  invIsoIdem : {x y : ob} → (f : CatIso C x y) → invIso (invIso f) ≡ f
  invIsoIdem f = refl


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

  ⋆IsoInvRev : {x y z : ob} → (f : CatIso C x y)(g : CatIso C y z) → invIso (⋆Iso f g) ≡ ⋆Iso (invIso g) (invIso f)
  ⋆IsoInvRev _ _ = refl


  pathToIso-∙ : {x y z : ob}(p : x ≡ y)(q : y ≡ z) → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q)
  pathToIso-∙ p q = J2 (λ y p z q → pathToIso (p ∙ q) ≡ ⋆Iso (pathToIso p) (pathToIso q)) pathToIso-∙-refl p q
    where
    pathToIso-∙-refl : {x : ob} → pathToIso {x = x} (refl ∙ refl) ≡ ⋆Iso (pathToIso refl) (pathToIso refl)
    pathToIso-∙-refl = cong pathToIso (sym compPathRefl)
      ∙ sym (⋆IsoIdL _)
      ∙ (λ i → ⋆Iso (pathToIso-refl (~ i)) (pathToIso refl))


  transportPathToIso : {x y z : ob}(f : C [ x , y ])(p : y ≡ z) → PathP (λ i → C [ x , p i ]) f (f ⋆ pathToIso {C = C} p .fst)
  transportPathToIso {x = x} f = J (λ _ p → PathP (λ i → C [ x , p i ]) f (f ⋆ pathToIso {C = C} p .fst))
    (sym (⋆IdR _) ∙ cong (λ x → f ⋆ x) (sym (cong fst (pathToIso-refl {C = C}))))


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


    transportIsoToPath : {x y z : ob}(f : C [ x , y ])(p : CatIso C y z)
      → PathP (λ i → C [ x , CatIsoToPath p i ]) f (f ⋆ p .fst)
    transportIsoToPath f p i =
      hcomp (λ j → λ
        { (i = i0) → f
        ; (i = i1) → f ⋆ secEq (univEquiv _ _) p j .fst })
      (transportPathToIso f (CatIsoToPath p) i)

    transportIsoToPathIso : {x y z : ob}(f : CatIso C x y)(p : CatIso C y z)
      → PathP (λ i → CatIso C x (CatIsoToPath p i)) f (⋆Iso f p)
    transportIsoToPathIso f p i .fst = transportIsoToPath (f .fst) p i
    transportIsoToPathIso f p i .snd =
      isProp→PathP (λ i → isPropIsIso (transportIsoToPath (f .fst) p i)) (f .snd) (⋆Iso f p .snd) i


    isoToPath-Square : {x y z w : ob}
      → (p : CatIso C x y)(q : CatIso C z w)
      → (f : Hom[ x , z ])(g : Hom[ y , w ])
      → f ⋆ q .fst ≡ p .fst ⋆ g
      → PathP (λ i → Hom[ CatIsoToPath p i , CatIsoToPath q i ]) f g
    isoToPath-Square p q f g comm =
      pathToIso-Square (CatIsoToPath p) (CatIsoToPath q) _ _
        ((λ i → f ⋆ secEq (univEquiv _ _) q i .fst) ∙ comm ∙ (λ i → secEq (univEquiv _ _) p (~ i) .fst ⋆ g))


module _ {C : Category ℓC ℓC'} where
  open Category C
  open isIso

  ⋆InvLMove : {x y z : ob}
    (f : CatIso C x y)
    {g : Hom[ y , z ]}{h : Hom[ x , z ]}
    → f .fst ⋆ g ≡ h
    → g ≡ f .snd .inv ⋆ h
  ⋆InvLMove f {g = g} p =
      sym (⋆IdL _)
    ∙ (λ i → f .snd .sec (~ i) ⋆ g)
    ∙ ⋆Assoc _ _ _
    ∙ (λ i → f .snd .inv ⋆ p i)

  ⋆InvRMove : {x y z : ob}
    (f : CatIso C y z)
    {g : Hom[ x , y ]}{h : Hom[ x , z ]}
    → g ⋆ f .fst ≡ h
    → g ≡ h ⋆ f .snd .inv
  ⋆InvRMove f {g = g} p =
      sym (⋆IdR _)
    ∙ (λ i → g ⋆ f .snd .ret (~ i))
    ∙ sym (⋆Assoc _ _ _)
    ∙ (λ i → p i ⋆ f .snd .inv)

  ⋆CancelL : {x y z : ob}
    (f : CatIso C x y){g h : Hom[ y , z ]}
    → f .fst ⋆ g ≡ f .fst ⋆ h
    → g ≡ h
  ⋆CancelL f {g = g} {h = h} p =
      sym (⋆IdL _)
    ∙ (λ i → f .snd .sec (~ i) ⋆ g)
    ∙ ⋆Assoc _ _ _
    ∙ (λ i → f .snd .inv ⋆ p i)
    ∙ sym (⋆Assoc _ _ _)
    ∙ (λ i → f .snd .sec i ⋆ h)
    ∙ ⋆IdL _

  ⋆CancelR : {x y z : ob}
    (f : CatIso C y z){g h : Hom[ x , y ]}
    → g ⋆ f .fst ≡ h ⋆ f .fst
    → g ≡ h
  ⋆CancelR f {g = g} {h = h} p =
      sym (⋆IdR _)
    ∙ (λ i → g ⋆ f .snd .ret (~ i))
    ∙ sym (⋆Assoc _ _ _)
    ∙ (λ i → p i ⋆ f .snd .inv)
    ∙ ⋆Assoc _ _ _
    ∙ (λ i → h ⋆ f .snd .ret i)
    ∙ ⋆IdR _

  ⋆InvLMove⁻ : {x y z : ob}
    (f : CatIso C x y)
    {g : Hom[ y , z ]}{h : Hom[ x , z ]}
    → g ≡ f .snd .inv ⋆ h
    → f .fst ⋆ g ≡ h
  ⋆InvLMove⁻ f {g = g} {h = h} p =
    cong (λ a → f .fst ⋆ a) p ∙
    sym (⋆Assoc _ _ _) ∙
    cong (λ a → a ⋆ h) (f .snd .ret) ∙
    ⋆IdL _

  ⋆InvRMove⁻ : {x y z : ob}
    (f : CatIso C y z)
    {g : Hom[ x , y ]}{h : Hom[ x , z ]}
    → g ≡ h ⋆ f .snd .inv
    → g ⋆ f .fst ≡ h
  ⋆InvRMove⁻ f {g = g} {h = h} p =
    cong (λ a → a ⋆ f .fst) p ∙
    ⋆Assoc _ _ _ ∙
    cong (λ a → h ⋆ a) (f .snd .sec) ∙
    ⋆IdR _

  ⋆InvsFlipSq : {w x y z : ob}
    (e : CatIso C w x)
    {g : Hom[ w , y ]}
    {h : Hom[ x , z ]}
    (f : CatIso C y z)
    → e .fst ⋆ h ≡ g ⋆ f .fst
    → h ⋆ f .snd .inv ≡ e .snd .inv ⋆ g
  ⋆InvsFlipSq e {g} {h} f p =
    ⋆InvLMove e
      (sym (⋆Assoc _ _ _)
      ∙ sym (⋆InvRMove f (sym p)))

  ⋆InvsFlipSq⁻ : {w x y z : ob}
    (e : CatIso C w x)
    {g : Hom[ w , y ]}
    {h : Hom[ x , z ]}
    (f : CatIso C y z)
    → h ⋆ f .snd .inv ≡ e .snd .inv ⋆ g
    → e .fst ⋆ h ≡ g ⋆ f .fst
  ⋆InvsFlipSq⁻ e f p = ⋆InvLMove⁻ e
    ( sym (⋆InvRMove⁻ f (sym p))
    ∙ ⋆Assoc _ _ _)

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

-- Univalent Categories

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{F : Functor C D} where
  module _ (isUnivC : isUnivalent C) (isUnivD : isUnivalent D) where
    open isUnivalent
    open Category
    open Functor
    isoToPathC = CatIsoToPath isUnivC
    isoToPathD = CatIsoToPath isUnivD

    F-isoToPath : {x y : C .ob} → (f : CatIso C x y) →
      isoToPathD (F-Iso {F = F} f) ≡ cong (F .F-ob) (isoToPathC f)
    F-isoToPath f = isoFunInjective (equivToIso (univEquiv isUnivD _ _)) _ _
      ( secEq (univEquiv isUnivD _ _) _
      ∙ sym (sym (F-pathToIso {F = F} (isoToPathC f))
      ∙ cong (F-Iso {F = F}) (secEq (univEquiv isUnivC _ _) f)))

module _ {C : Category ℓC ℓC'} (isUnivC : isUnivalent C) where
  open Category
  open Functor
  open isUnivalent
  op-Iso-pathToIso : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p
  op-Iso-pathToIso =
    J (λ y p → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p)
      (CatIso≡ _ _ refl)

  op-Iso-pathToIso' : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso (pathToIso {C = C ^op} p) ≡ pathToIso {C = C} p
  op-Iso-pathToIso' =
    J (λ y p → op-Iso (pathToIso {C = C ^op} p) ≡ pathToIso {C = C} p)
      (CatIso≡ _ _ refl)

  isUnivalentOp : isUnivalent (C ^op)
  isUnivalentOp .univ x y = isIsoToIsEquiv
    ( (λ f^op → CatIsoToPath isUnivC (op-Iso f^op))
    , (λ f^op → CatIso≡ _ _
        (cong fst
        (cong op-Iso ((secEq (univEquiv isUnivC _ _) (op-Iso f^op))))))
    , λ p → cong (CatIsoToPath isUnivC) (op-Iso-pathToIso' p)
        ∙ retEq (univEquiv isUnivC _ _) p)
