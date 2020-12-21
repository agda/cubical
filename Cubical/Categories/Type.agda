{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

open Precategory

module _ ℓ where
  TYPE : Precategory (ℓ-suc ℓ) ℓ
  TYPE .ob = Type ℓ
  TYPE .Hom[_,_] A B = A → B
  TYPE .id A  = λ x → x
  TYPE ._⋆_ f g = λ x → g (f x)
  TYPE .⋆IdL f = refl
  TYPE .⋆IdR f = refl
  TYPE .⋆Assoc f g h = refl
