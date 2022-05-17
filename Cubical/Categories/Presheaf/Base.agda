{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors

private
  variable
    ℓ ℓ' ℓS : Level

Presheaf : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
Presheaf C ℓS = Functor (C ^op) (SET ℓS)

PresheafCategory : ∀ {ℓ ℓ'} → Category ℓ ℓ' → (ℓS : Level)
       → Category (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
                  (ℓ-max (ℓ-max ℓ ℓ') ℓS)
PresheafCategory C ℓS = FUNCTOR (C ^op) (SET ℓS)
