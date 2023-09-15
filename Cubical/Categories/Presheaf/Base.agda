{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base

private
  variable
    ℓ ℓ' ℓS : Level

Presheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
Presheaf C ℓS = Functor (C ^op) (SET ℓS)

PresheafCategory : Category ℓ ℓ' → (ℓS : Level)
       → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
                  (ℓ-max (ℓ-max ℓ ℓ') ℓS)
PresheafCategory C ℓS = FUNCTOR (C ^op) (SET ℓS)

isUnivalentPresheafCategory : {C : Category ℓ ℓ'} → isUnivalent (PresheafCategory C ℓS)
isUnivalentPresheafCategory = isUnivalentFUNCTOR _ _ isUnivalentSET
