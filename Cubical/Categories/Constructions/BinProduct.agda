-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level


open Category

_×_ : (C : Category ℓC ℓC') → (D : Category ℓD ℓD')
    → Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

(C × D) .ob = (ob C) ×' (ob D)
(C × D) .Hom[_,_] (c , d) (c' , d') = (C [ c , c' ]) ×' (D [ d , d' ])
(C × D) .id = (id C , id D)
(C × D) ._⋆_ _ _ = (_ ⋆⟨ C ⟩ _ , _ ⋆⟨ D ⟩ _)
(C × D) .⋆IdL _ = ≡-× (⋆IdL C _) (⋆IdL D _)
(C × D) .⋆IdR _ = ≡-× (⋆IdR C _) (⋆IdR D _)
(C × D) .⋆Assoc _ _ _ = ≡-× (⋆Assoc C _ _ _) (⋆Assoc D _ _ _)
(C × D) .isSetHom = isSet× (isSetHom C) (isSetHom D)

infixr 5 _×_


-- Some useful functors
module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor

  module _ (E : Category ℓE ℓE') where
    -- Associativity of product
    ×C-assoc : Functor (C × (D × E)) ((C × D) × E)
    ×C-assoc .F-ob (c , (d , e)) = ((c , d), e)
    ×C-assoc .F-hom (f , (g , h)) = ((f , g), h)
    ×C-assoc .F-id = refl
    ×C-assoc .F-seq _ _ = refl

  -- Left/right injections into product
  linj : (d : ob D) → Functor C (C × D)
  linj d .F-ob c = (c , d)
  linj d .F-hom f = (f , id D)
  linj d .F-id = refl
  linj d .F-seq f g = ≡-× refl (sym (⋆IdL D _))

  rinj : (c : ob C) → Functor D (C × D)
  rinj c .F-ob d = (c , d)
  rinj c .F-hom f = (id C , f)
  rinj c .F-id = refl
  rinj c .F-seq f g = ≡-× (sym (⋆IdL C _)) refl

{-
  TODO:
    - define inverse to `assoc`, prove isomorphism
    - prove product is commutative up to isomorphism
-}
