-- Binary coproducts
{-# OPTIONS --safe #-}

module Cubical.Categories.Colimits.Coproduct where

open import Cubical.Categories.Category.Base using (Precategory; _^op)
open import Cubical.Categories.Limits.Product using (isProduct)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max)

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C

  module _ {x y : ob} where
    isCoproduct : {x+y : ob} (i₁ : Hom[ x , x+y ]) (i₂ : Hom[ y , x+y ]) → Type (ℓ-max ℓ ℓ')
    isCoproduct = isProduct {C = C ^op}