-- Binary products
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.BinProduct where

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

    isBinProduct : Type (ℓ-max ℓ ℓ')
    isBinProduct = ∀ {z : ob} (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
        ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)

    isPropIsBinProduct : isProp (isBinProduct)
    isPropIsBinProduct = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsContr))


  record BinProduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      binProdOb : ob
      binProdPr₁ : Hom[ binProdOb , x ]
      binProdPr₂ : Hom[ binProdOb , y ]
      univProp : isBinProduct binProdPr₁ binProdPr₂


  BinProducts : Type (ℓ-max ℓ ℓ')
  BinProducts = (x y : ob) → BinProduct x y

  hasBinProducts : Type (ℓ-max ℓ ℓ')
  hasBinProducts = ∥ BinProducts ∥₁
