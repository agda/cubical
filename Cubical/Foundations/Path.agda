{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Set ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f
