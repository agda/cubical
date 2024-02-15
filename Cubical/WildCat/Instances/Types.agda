{-# OPTIONS --safe #-}
module Cubical.WildCat.Instances.Types where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (⋆ ; id)
open import Cubical.Foundations.Function using (idfun) renaming (_∘_ to _∘fun_)

open import Cubical.WildCat.Base

private
  variable
    ℓ ℓ' : Level

open WildCat

-- Instances
module _ (ℓ : Level) where
  TypeCat : WildCat (ℓ-suc ℓ) ℓ
  ob TypeCat = Type ℓ
  Hom[_,_] TypeCat A B = A → B
  WildCat.id TypeCat = idfun _
  _⋆_ TypeCat f g = g ∘fun f
  ⋆IdL TypeCat = λ _ → refl
  ⋆IdR TypeCat = λ _ → refl
  ⋆Assoc TypeCat f g h = refl
