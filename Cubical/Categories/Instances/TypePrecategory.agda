{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.TypePrecategory where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Precategory

open Precategory

-- TYPE precategory has types as objects
module _ ℓ where
  TYPE : Precategory (ℓ-suc ℓ) ℓ
  TYPE .ob           = Type ℓ
  TYPE .Hom[_,_] A B = A → B
  TYPE .id           = λ x → x
  TYPE ._⋆_ f g      = λ x → g (f x)
  TYPE .⋆IdL f       = refl
  TYPE .⋆IdR f       = refl
  TYPE .⋆Assoc f g h = refl
