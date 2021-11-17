{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A : Type ℓ

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∃[ n ∈ ℕ ] A ≃ Fin n

-- finite sets are sets
isFinSet→isSet : isFinSet A → isSet A
isFinSet→isSet = rec isPropIsSet (λ (_ , p) → isOfHLevelRespectEquiv 2 (invEquiv p) isSetFin)

isPropIsFinSet : isProp (isFinSet A)
isPropIsFinSet = isPropPropTrunc

-- the type of finite sets

FinSet : (ℓ : Level) → Type (ℓ-suc ℓ)
FinSet ℓ = TypeWithStr _ isFinSet
