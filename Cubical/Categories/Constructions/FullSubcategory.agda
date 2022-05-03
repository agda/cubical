{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FullSubcategory where
-- Full subcategory (not necessarily injective on objects)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓC ℓC' ℓP : Level

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
