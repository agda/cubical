{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open Category

module Cubical.Categories.Instances.Slice
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  (c : C .ob)
  where

open import Cubical.Categories.Instances.Slice.Base C c public
open import Cubical.Categories.Instances.Slice.Properties C c public
