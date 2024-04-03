{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Limits

open Category hiding (_∘_)

module _ ℓ where
  SET : Category (ℓ-suc ℓ) ℓ
  ob SET = hSet ℓ
  Hom[_,_] SET (A , _) (B , _) = A → B
  id SET x = x
  _⋆_ SET f g x = g (f x)
  ⋆IdL SET f = refl
  ⋆IdR SET f = refl
  ⋆Assoc SET f g h = refl
  isSetHom SET {A} {B} = isSetΠ (λ _ → snd B)

private
  variable
    ℓ ℓ' : Level

open Functor

-- Hom functors
_[-,_] : (C : Category ℓ ℓ') → (c : C .ob) → Functor (C ^op) (SET ℓ')
(C [-, c ]) .F-ob x    = (C [ x , c ]) , C .isSetHom
(C [-, c ]) .F-hom f k = f ⋆⟨ C ⟩ k
(C [-, c ]) .F-id      = funExt λ _ → C .⋆IdL _
(C [-, c ]) .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

_[_,-] : (C : Category ℓ ℓ') → (c : C .ob)→ Functor C (SET ℓ')
(C [ c ,-]) .F-ob x    = (C [ c , x ]) , C .isSetHom
(C [ c ,-]) .F-hom f k = k ⋆⟨ C ⟩ f
(C [ c ,-]) .F-id      = funExt λ _ → C .⋆IdR _
(C [ c ,-]) .F-seq _ _ = funExt λ _ → sym (C .⋆Assoc _ _ _)

-- Lift functor
LiftF : Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
LiftF {ℓ}{ℓ'} .F-ob A = (Lift {ℓ}{ℓ'} (A .fst)) , isOfHLevelLift 2 (A .snd)
LiftF .F-hom f x = lift (f (x .lower))
LiftF .F-id = refl
LiftF .F-seq f g = funExt λ x → refl

module _ {C : Category ℓ ℓ'} {F : Functor C (SET ℓ')} where
  open NatTrans

  -- natural transformations by pre/post composition
  preComp : {x y : C .ob}
          → (f : C [ x , y ])
          → C [ x ,-] ⇒ F
          → C [ y ,-] ⇒ F
  preComp f α .N-ob c k = (α ⟦ c ⟧) (f ⋆⟨ C ⟩ k)
  preComp f α .N-hom {x = c} {d} k
    = (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ (l ⋆⟨ C ⟩ k)))
    ≡[ i ]⟨ (λ l → (α ⟦ d ⟧) (⋆Assoc C f l k (~ i))) ⟩
      (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ l ⋆⟨ C ⟩ k))
    ≡[ i ]⟨ (λ l → (α .N-hom k) i (f ⋆⟨ C ⟩ l)) ⟩
      (λ l → (F ⟪ k ⟫) ((α ⟦ c ⟧) (f ⋆⟨ C ⟩ l)))
    ∎

-- properties
-- TODO: move to own file
open isIso renaming (inv to cInv)
open Iso

module _ {A B : (SET ℓ) .ob } where

  Iso→CatIso : Iso (fst A) (fst B)
             → CatIso (SET ℓ) A B
  Iso→CatIso is .fst = is .fun
  Iso→CatIso is .snd .cInv = is .inv
  Iso→CatIso is .snd .sec = funExt λ b → is .rightInv b -- is .rightInv
  Iso→CatIso is .snd .ret = funExt λ b → is .leftInv b -- is .rightInv

  CatIso→Iso : CatIso (SET ℓ) A B
             → Iso (fst A) (fst B)
  CatIso→Iso cis .fun = cis .fst
  CatIso→Iso cis .inv = cis .snd .cInv
  CatIso→Iso cis .rightInv = funExt⁻ λ b → cis .snd .sec b
  CatIso→Iso cis .leftInv  = funExt⁻ λ b → cis .snd .ret b


  Iso-Iso-CatIso : Iso (Iso (fst A) (fst B)) (CatIso (SET ℓ) A B)
  fun Iso-Iso-CatIso = Iso→CatIso
  inv Iso-Iso-CatIso = CatIso→Iso
  rightInv Iso-Iso-CatIso b = refl
  fun (leftInv Iso-Iso-CatIso a i) = fun a
  inv (leftInv Iso-Iso-CatIso a i) = inv a
  rightInv (leftInv Iso-Iso-CatIso a i) = rightInv a
  leftInv (leftInv Iso-Iso-CatIso a i) = leftInv a

  Iso-CatIso-≡ : Iso (CatIso (SET ℓ) A B) (A ≡ B)
  Iso-CatIso-≡ = compIso (invIso Iso-Iso-CatIso) (hSet-Iso-Iso-≡ _ _)

-- SET is univalent

isUnivalentSET : isUnivalent {ℓ' = ℓ} (SET _)
isUnivalent.univ isUnivalentSET (A , isSet-A) (B , isSet-B)  =
   precomposesToId→Equiv
      pathToIso _ (funExt w) (isoToIsEquiv Iso-CatIso-≡)
   where
     w : _
     w ci =
       invEq
         (congEquiv (isoToEquiv (invIso Iso-Iso-CatIso)))
         (SetsIso≡-ext isSet-A isSet-B
            (λ x i → transp (λ _ → B) i (ci .fst (transp (λ _ → A) i x)))
            (λ x i → transp (λ _ → A) i (ci .snd .cInv (transp (λ _ → B) i x))))

-- SET is complete

open LimCone
open Cone

completeSET : ∀ {ℓJ ℓJ'} → Limits {ℓJ} {ℓJ'} (SET (ℓ-max ℓJ ℓJ'))
lim (completeSET J D) = Cone D (Unit* , isOfHLevelLift 2 isSetUnit) , isSetCone D _
coneOut (limCone (completeSET J D)) j e = coneOut e j tt*
coneOutCommutes (limCone (completeSET J D)) j i e = coneOutCommutes e j i tt*
univProp (completeSET J D) c cc =
  uniqueExists
    (λ x → cone (λ v _ → coneOut cc v x) (λ e i _ → coneOutCommutes cc e i x))
    (λ _ → funExt (λ _ → refl))
    (λ x → isPropIsConeMor cc (limCone (completeSET J D)) x)
    (λ x hx → funExt (λ d → cone≡ λ u → funExt (λ _ → sym (funExt⁻ (hx u) d))))

module _ {ℓ} where

 open Pullback

 PullbacksSET : Pullbacks (SET ℓ)
 PullbacksSET (cospan l m r s₁ s₂) = pb
  where
  pb : Pullback (SET ℓ) (cospan l m r s₁ s₂)
  pbOb pb = _ , isSetΣ (isSet× (snd l) (snd r))
   (uncurry λ x y → isOfHLevelPath 2 (snd m) (s₁ x) (s₂ y))
  pbPr₁ pb = fst ∘ fst
  pbPr₂ pb = snd ∘ fst
  pbCommutes pb = funExt snd
  fst (fst (univProp pb h k H')) d = _ , (H' ≡$ d)
  snd (fst (univProp pb h k H')) = refl , refl
  snd (univProp pb h k H') y =
   Σ≡Prop
    (λ _ → isProp× (isSet→ (snd l) _ _) (isSet→ (snd r) _ _))
     (funExt λ x → Σ≡Prop (λ _ → (snd m) _ _)
        λ i → fst (snd y) i x , snd (snd y) i x)
