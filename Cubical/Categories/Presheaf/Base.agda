{-# OPTIONS --postfix-projections --safe #-}

module Cubical.Categories.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors

module _ {ℓ ℓ'} where

  PreShv : Precategory ℓ ℓ' → (ℓS : Level)
         → Precategory (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS)) (ℓ-max (ℓ-max ℓ ℓ') ℓS)
  PreShv C ℓS = FUNCTOR (C ^op) (SET ℓS)

instance
  isCatPreShv : ∀ {ℓ ℓ'} {C : Precategory ℓ ℓ'} {ℓS}
    → isCategory (PreShv C ℓS)
  isCatPreShv {C = C} {ℓS} = isCatFUNCTOR (C ^op) (SET ℓS)
