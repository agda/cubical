{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.FullSubcategory where
-- Full subcategory (not necessarily injective on objects)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR : Level

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

module _ (C : Category ℓC ℓC') (P : Category.ob C → Type ℓP)
         (D : Category ℓD ℓD') (Q : Category.ob D → Type ℓQ)
         (E : Category ℓE ℓE') (R : Category.ob E → Type ℓR) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
  open Category
  open Functor

  MapFullSubcategory-seq :
    (F : Functor C D) → (f : (c : C.ob) → P c → Q (F-ob F c)) →
    (G : Functor D E) → (g : (d : D.ob) → Q d → R (F-ob G d)) →
    MapFullSubcategory C P E R (funcComp G F) (λ c p → g (F-ob F c) (f c p)) ≡
    funcComp
      (MapFullSubcategory D Q E R G g)
      (MapFullSubcategory C P D Q F f)
  MapFullSubcategory-seq F f G g = Functor≡
    (λ (c , p) → refl)
    (λ γ → refl)
