-- Coequalisers
{-# OPTIONS --safe #-}

module Cubical.Categories.Colimits.Coequaliser where

open import Cubical.Categories.Category.Base using (Precategory; _^op)
open import Cubical.Categories.Limits.Equaliser using (isEqualiser)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max)

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C

  module _ {x y : ob} where
    module _ {z : ob} where
      isCoequaliser : Hom[ y , z ] → (f g : Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
      isCoequaliser = isEqualiser {C = C ^op}