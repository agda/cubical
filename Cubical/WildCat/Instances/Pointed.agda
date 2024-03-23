{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (⋆ ; id)

open import Cubical.WildCat.Base

open WildCat

PointedCat : (ℓ : Level) → WildCat (ℓ-suc ℓ) ℓ
ob (PointedCat ℓ) = Pointed ℓ
Hom[_,_] (PointedCat ℓ) A B = A →∙ B
WildCat.id (PointedCat ℓ) = idfun∙ _
_⋆_ (PointedCat ℓ) f g = g ∘∙ f
⋆IdL (PointedCat ℓ) = ∘∙-idˡ
⋆IdR (PointedCat ℓ) = ∘∙-idʳ
⋆Assoc (PointedCat ℓ) f g h = sym (∘∙-assoc h g f)
