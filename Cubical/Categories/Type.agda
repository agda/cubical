{-# OPTIONS --cubical --safe #-}

module Cubical.Categories.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module _ ℓ where
  TYPE : Precategory (ℓ-suc ℓ) ℓ
  TYPE .ob = Type ℓ
  TYPE .hom A B = A → B
  TYPE .idn A  = λ x → x
  TYPE .seq f g = λ x → g (f x)
  TYPE .seq-λ f = refl
  TYPE .seq-ρ f = refl
  TYPE .seq-α f g h = refl
