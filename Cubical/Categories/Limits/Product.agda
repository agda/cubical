-- Binary products
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Product where

open import Cubical.Categories.Category.Base using (Precategory)
open import Cubical.Data.Sigma.Base using (∃!-syntax) renaming (_×_ to _∧_)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max; _≡_)

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C

  module _ {x y : ob} where

    record Span : Type (ℓ-max ℓ ℓ') where
      constructor span
      field
        z : ob
        f₁ : Hom[ z , x ]
        f₂ : Hom[ z , y ]

    record isProduct' (P : Span) : Type (ℓ-max ℓ ℓ') where
      open Span P renaming (z to x×y; f₁ to π₁; f₂ to π₂)

      field
        univProp : (Q : Span) →
          let open Span Q in
          ∃![ f ∈ Hom[ z , x×y ] ]
            (π₁ ∘ f ≡ f₁) ∧ (π₂ ∘ f ≡ f₂)
    
    isProduct : {x×y : ob} (π₁ : Hom[ x×y , x ]) (π₂ : Hom[ x×y , y ]) → Type (ℓ-max ℓ ℓ')
    isProduct {x×y} π₁ π₂ = isProduct' (span x×y π₁ π₂)


-- TODO: define products using isLimit from Cubical.Categories.Limits.Base
--   and show this gives the same thing