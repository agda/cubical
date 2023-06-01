{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open Category

module Cubical.Categories.Constructions.Slice
  {ℓ ℓ' : Level}
  (C : Category ℓ ℓ')
  (c : C .ob)
  where

open import Cubical.Categories.Constructions.Slice.Base C c public
open import Cubical.Categories.Constructions.Slice.Properties C c public
