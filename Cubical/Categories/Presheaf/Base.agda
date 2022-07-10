{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

private
  variable
    ℓ ℓ' ℓS : Level

PreShv : Category ℓ ℓ' → (ℓS : Level)
       → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
                  (ℓ-max (ℓ-max ℓ ℓ') ℓS)
PreShv C ℓS = FUNCTOR (C ^op) (SET ℓS)

-- Presheaf Category is Univalent

isUnivalentPreShv : {C : Category ℓ ℓ'} → isUnivalent (PreShv C ℓS)
isUnivalentPreShv = isUnivalentFUNCTOR _ _ isUnivalentSET
