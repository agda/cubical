{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Limits

open Category

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
open CatIso renaming (inv to cInv)
open Iso

Iso→CatIso : ∀ {A B : (SET ℓ) .ob}
           → Iso (fst A) (fst B)
           → CatIso (SET ℓ) A B
Iso→CatIso is .mor = is .fun
Iso→CatIso is .cInv = is .inv
Iso→CatIso is .sec = funExt λ b → is .rightInv b -- is .rightInv
Iso→CatIso is .ret = funExt λ b → is .leftInv b -- is .rightInv

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
