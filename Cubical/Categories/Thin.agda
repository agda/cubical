{-# OPTIONS --safe #-}
module Cubical.Categories.Thin where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open Category

private
  variable ℓ ℓ' : Level

isThin : (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
isThin C = (x y : C .ob) → isProp (C [ x , y ])
