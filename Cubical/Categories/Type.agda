{-# OPTIONS --cubical #-}

module Cubical.Categories.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module _ ℓ where
  TYPE : Precategory (ℓ-suc ℓ)
  TYPE .ob = Type _
  TYPE .hom A B = Lift (A → B)
  TYPE .idn A .lower x = x
  TYPE .seq (lift f) (lift g) .lower x = g (f x)
  TYPE .seq-λ f = refl
  TYPE .seq-ρ f = refl
  TYPE .seq-α f g h = refl
