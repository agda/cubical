-- Binary products
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Product where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ {x y x×y : ob}
           (π₁ : Hom[ x×y , x ])
           (π₂ : Hom[ x×y , y ]) where

    isProduct : Type (ℓ-max ℓ ℓ')
    isProduct = ∀ (z : ob) (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
        ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)

    isPropIsProduct : isProp (isProduct)
    isPropIsProduct = isPropΠ3 λ z f₁ f₂ → isPropIsContr


  record Product (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      x×y : ob
      π₁ : Hom[ x×y , x ]
      π₂ : Hom[ x×y , y ]
      univ : isProduct π₁ π₂


  Products : Type (ℓ-max ℓ ℓ')
  Products = (x y : ob) → Product x y

  hasProducts : Type (ℓ-max ℓ ℓ')
  hasProducts = ∥ Products ∥

-- -- TODO: define products using isLimit from Cubical.Categories.Limits.Base
-- --   and show this gives the same thing
