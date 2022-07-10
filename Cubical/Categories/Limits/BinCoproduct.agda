-- Binary coproducts
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.BinCoproduct where

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

  module _ {x y x+y : ob}
           (i₁ : Hom[ x , x+y ])
           (i₂ : Hom[ y , x+y ]) where

    isBinCoproduct : Type (ℓ-max ℓ ℓ')
    isBinCoproduct = ∀ {z : ob} (f₁ : Hom[ x , z ]) (f₂ : Hom[ y , z ]) →
        ∃![ f ∈ Hom[ x+y , z ] ] (i₁ ⋆ f ≡ f₁) × (i₂ ⋆ f ≡ f₂)

    isPropIsBinCoproduct : isProp (isBinCoproduct)
    isPropIsBinCoproduct = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsContr))


  record BinCoproduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      binCoprodOb : ob
      binCoprodInj₁ : Hom[ x , binCoprodOb ]
      binCoprodInj₂ : Hom[ y , binCoprodOb ]
      univProp : isBinCoproduct binCoprodInj₁ binCoprodInj₂


  BinCoproducts : Type (ℓ-max ℓ ℓ')
  BinCoproducts = (x y : ob) → BinCoproduct x y

  hasBinCoproducts : Type (ℓ-max ℓ ℓ')
  hasBinCoproducts = ∥ BinCoproducts ∥₁
