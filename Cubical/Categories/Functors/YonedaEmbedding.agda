{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.YonedaEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Instances.Functors.Currying

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where

  YonedaEmbedding : Functor C (PresheafCategory C ℓC')
  YonedaEmbedding = λF (C ^op) (SET ℓC') C (funcComp (HomFunctor C) (×C-sym C (C ^op)))
