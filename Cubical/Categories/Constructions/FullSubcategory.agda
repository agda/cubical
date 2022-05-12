{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FullSubcategory where
-- Full subcategory (not necessarily injective on objects)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ : Level

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP) where
  private
    module C = Category C
  open Category
  open Functor

  FullSubcategory : Category (ℓ-max ℓC ℓP) ℓC'
  ob FullSubcategory = Σ[ x ∈ C.ob ] P x
  Hom[_,_] FullSubcategory (x , p) (y , q) = C.Hom[ x , y ]
  id FullSubcategory = C.id
  _⋆_ FullSubcategory = C._⋆_
  ⋆IdL FullSubcategory = C.⋆IdL
  ⋆IdR FullSubcategory = C.⋆IdR
  ⋆Assoc FullSubcategory = C.⋆Assoc
  isSetHom FullSubcategory = C.isSetHom

  FullInclusion : Functor FullSubcategory C
  F-ob FullInclusion = fst
  F-hom FullInclusion = idfun _
  F-id FullInclusion = refl
  F-seq FullInclusion f g = refl

module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ) where
  private
    module C = Category C
    module D = Category D
  open Category
  open Functor

  ToFullSubcategory  : (F : Functor C D) → ((c : C.ob) → Q (F-ob F c)) → Functor C (FullSubcategory D Q)
  F-ob (ToFullSubcategory F f) c = F-ob F c , f c
  F-hom (ToFullSubcategory F f) = F-hom F
  F-id (ToFullSubcategory F f) = F-id F
  F-seq (ToFullSubcategory F f) = F-seq F

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP)
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ) where
  private
    module C = Category C
    module D = Category D
  open Category
  open Functor

  MapFullSubcategory : (F : Functor C D) → ((c : C.ob) → P c → Q (F-ob F c))
    → Functor (FullSubcategory C P) (FullSubcategory D Q)
  MapFullSubcategory F f = ToFullSubcategory (FullSubcategory C P) D Q
    (funcComp F (FullInclusion C P) )
    λ (c , p) → f c p
