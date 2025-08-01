{-
  The vertical category over an object from a displayed
  category. Also sometimes called the "fiber"
-}
module Cubical.Categories.Constructions.Vertical where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Constructions.DisplayOverTerminal
open import Cubical.Categories.Instances.Terminal

private
  variable
    ℓC ℓ'C ℓD ℓ'D ℓCᴰ ℓ'Cᴰ ℓDᴰ ℓ'Dᴰ : Level

module _ {C : Category ℓC ℓ'C} (Cᴰ : Categoryᴰ C ℓCᴰ ℓ'Cᴰ) where
  open Category C
  open Categoryᴰ Cᴰ
  VerticalCategory : ob → Category ℓCᴰ ℓ'Cᴰ
  VerticalCategory c = DispOverTerminal→Category
    (reindex Cᴰ (FunctorFromTerminal {ℓ* = ℓ-zero} c))
