-- Equalisers
{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Equaliser where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ {x y : ob} where
    private module _ (f g : Hom[ x , y ]) where

      record Equalises : Type (ℓ-max ℓ ℓ') where
        constructor equ
        field
          w : ob
          m : Hom[ w , x ]
          H : f ∘ m ≡ g ∘ m

      record IsEqualiser' (E : Equalises) : Type (ℓ-max ℓ ℓ') where
        open Equalises E renaming (w to e; m to eq)

        field
          univProp : (Q : Equalises) →
            let open Equalises Q in
            ∃![ u ∈ Hom[ w , e ] ]  eq ∘ u ≡ m


    module _ {w : ob} where

      IsEqualiser : Hom[ w , x ] → (f g : Hom[ x , y ]) → Type (ℓ-max ℓ ℓ')
      IsEqualiser k f g =
        Σ[ H ∈ f ∘ k ≡ g ∘ k ]
        IsEqualiser' f g (equ w k H)


-- TODO: define equalisers using isLimit from Cubical.Categories.Limits.Base
--   and show this gives the same thing
