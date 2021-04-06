{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open Precategory

module _ ℓ where
  SET : Precategory (ℓ-suc ℓ) ℓ
  SET .ob = Σ (Type ℓ) isSet
  SET .Hom[_,_] (A , _) (B , _) = A → B
  SET .id _  = λ x → x
  SET ._⋆_ f g = λ x → g (f x)
  SET .⋆IdL f = refl
  SET .⋆IdR f = refl
  SET .⋆Assoc f g h = refl

module _ {ℓ} where
  isSetExpIdeal : {A B : Type ℓ} → isSet B → isSet (A → B)
  isSetExpIdeal B/set = isSetΠ λ _ → B/set

  isSetLift : {A : Type ℓ} → isSet A → isSet (Lift {ℓ} {ℓ-suc ℓ} A)
  isSetLift = isOfHLevelLift 2

  module _ {A B : SET ℓ .ob} where
    -- monic/surjectiveness
    open import Cubical.Categories.Morphism
    isSurjSET : (f : SET ℓ [ A , B ]) → Type _
    isSurjSET f = ∀ (b : fst B) → Σ[ a ∈ fst A ] f a ≡ b

    -- isMonic→isSurjSET : {f : SET ℓ [ A , B ]}
    --                   → isEpic {C = SET ℓ} {x = A} {y = B} f
    --                   → isSurjSET f
    -- isMonic→isSurjSET ism b = {!!} , {!!}

  instance
    SET-category : isCategory (SET ℓ)
    SET-category .isSetHom {_} {B , B/set} = isSetExpIdeal B/set

private
  variable
    ℓ ℓ' : Level

open Functor

-- Hom functors
_[-,_] : (C : Precategory ℓ ℓ') → (c : C .ob) → ⦃ isCat : isCategory C ⦄ → Functor (C ^op) (SET ℓ')
(C [-, c ]) ⦃ isCat ⦄ .F-ob x = (C [ x , c ]) , isCat .isSetHom
(C [-, c ])           .F-hom f k = f ⋆⟨ C ⟩ k
(C [-, c ])           .F-id = funExt λ _ → C .⋆IdL _
(C [-, c ])           .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

_[_,-] : (C : Precategory ℓ ℓ') → (c : C .ob) → ⦃ isCat : isCategory C ⦄ → Functor C (SET ℓ')
(C [ c ,-]) ⦃ isCat ⦄ .F-ob x = (C [ c , x ]) , isCat .isSetHom
(C [ c ,-])           .F-hom f k = k ⋆⟨ C ⟩ f
(C [ c ,-])           .F-id = funExt λ _ → C .⋆IdR _
(C [ c ,-])           .F-seq _ _ = funExt λ _ → sym (C .⋆Assoc _ _ _)

module _ {C : Precategory ℓ ℓ'} ⦃ _ : isCategory C ⦄ {F : Functor C (SET ℓ')} where
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
           → CatIso {C = SET ℓ} A B
Iso→CatIso is .mor = is .fun
Iso→CatIso is .cInv = is .inv
Iso→CatIso is .sec = funExt λ b → is .rightInv b -- is .rightInv
Iso→CatIso is .ret = funExt λ b → is .leftInv b -- is .rightInv


-- TYPE category is has all types as objects
-- kind of useless
module _ ℓ where
  TYPE : Precategory (ℓ-suc ℓ) ℓ
  TYPE .ob = Type ℓ
  TYPE .Hom[_,_] A B = A → B
  TYPE .id A  = λ x → x
  TYPE ._⋆_ f g = λ x → g (f x)
  TYPE .⋆IdL f = refl
  TYPE .⋆IdR f = refl
  TYPE .⋆Assoc f g h = refl
