{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

Constant : (C : Category ℓC ℓC') (D : Category ℓD ℓD') (d : ob D) → Functor C D
F-ob (Constant C D d) c = d
F-hom (Constant C D d) φ = id D
F-id (Constant C D d) = refl
F-seq (Constant C D d) φ χ = sym (⋆IdR D _)
