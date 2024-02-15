{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (⋆ ; id)

open import Cubical.WildCat.Base

private
  variable
    ℓ ℓ' : Level

open WildCat

-- Instances
module _ (ℓ : Level) where
  PointedCat : WildCat (ℓ-suc ℓ) ℓ
  ob PointedCat = Pointed ℓ
  Hom[_,_] PointedCat A B = A →∙ B
  WildCat.id PointedCat = idfun∙ _
  _⋆_ PointedCat f g = g ∘∙ f
  ⋆IdL PointedCat = ∘∙-idˡ
  ⋆IdR PointedCat = ∘∙-idʳ
  ⋆Assoc PointedCat f g h = sym (∘∙-assoc h g f)
