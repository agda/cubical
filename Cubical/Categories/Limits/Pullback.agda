{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Limits.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan


private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where

  PullbackDiagram : Type (ℓ-max ℓ ℓ')
  PullbackDiagram = Functor Cospan C
