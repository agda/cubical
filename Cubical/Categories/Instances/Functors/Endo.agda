{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base renaming (𝟙⟨_⟩ to idfunctor)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

module Cubical.Categories.Instances.Functors.Endo {ℓC ℓC'} (C : Category ℓC ℓC') where

  open Category
  open NatTrans
  open Functor
  open StrictMonStr
  open TensorStr

  EndofunctorCategory : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC ℓC')
  EndofunctorCategory = FUNCTOR C C
