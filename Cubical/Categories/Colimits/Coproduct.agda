-- Binary coproducts
{-# OPTIONS --safe #-}

module Cubical.Categories.Colimits.Coproduct where

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

    isCoproduct : Type (ℓ-max ℓ ℓ')
    isCoproduct = ∀ (z : ob) (f₁ : Hom[ x , z ]) (f₂ : Hom[ y , z ]) →
        ∃![ f ∈ Hom[ x+y , z ] ] (i₁ ⋆ f ≡ f₁) × (i₂ ⋆ f ≡ f₂)

    isPropIsCoproduct : isProp (isCoproduct)
    isPropIsCoproduct = isPropΠ3 λ z f₁ f₂ → isPropIsContr


  record Coproduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      x+y : ob
      i₁ : Hom[ x , x+y ]
      i₂ : Hom[ y , x+y ]
      univ : isCoproduct i₁ i₂


  Coproducts : Type (ℓ-max ℓ ℓ')
  Coproducts = (x y : ob) → Coproduct x y

  hasCoproducts : Type (ℓ-max ℓ ℓ')
  hasCoproducts = ∥ Coproducts ∥
