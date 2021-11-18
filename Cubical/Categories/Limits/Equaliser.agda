-- Equalisers
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Equaliser where

open import Cubical.Categories.Category.Base using (Precategory)
open import Cubical.Data.Sigma.Base using (∃!-syntax; Σ-syntax)
open import Cubical.Foundations.Prelude using (Level; Type; ℓ-max; _≡_)

private
  variable
    ℓ ℓ' : Level

module _ {C : Precategory ℓ ℓ'} where
  open Precategory C

  module _ {x y : ob} where
    module _ (f g : Hom[ x , y ]) where

      record Equalises : Type (ℓ-max ℓ ℓ') where
        constructor equ
        field
          w : ob
          m : Hom[ w , x ]
          H : f ∘ m ≡ g ∘ m

      record isEqualiser' (E : Equalises) : Type (ℓ-max ℓ ℓ') where
        open Equalises E renaming (w to e; m to eq)

        field
          univProp : (Q : Equalises) →
            let open Equalises Q in
            ∃![ u ∈ Hom[ w , e ] ]  eq ∘ u ≡ m
  
  
    module _ {w : ob} where

      isEqualiser : Hom[ w , x ] → (f g : Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
      isEqualiser k f g =
        Σ[ H ∈ f ∘ k ≡ g ∘ k ]
        isEqualiser' f g (equ w k H)


-- TODO: define equalisers using isLimit from Cubical.Categories.Limits.Base
--   and show this gives the same thing