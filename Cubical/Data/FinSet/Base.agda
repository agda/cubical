{-

Definition of finite sets

There are may different formulations of finite sets in constructive mathematics,
and we will use Bishop finiteness as is called by some people in the literature.

-}
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

-- definition of (Bishop) finite sets

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∃[ n ∈ ℕ ] A ≃ Fin n

-- finite sets are sets
isFinSet→isSet : isFinSet A → isSet A
isFinSet→isSet = rec isPropIsSet (λ (_ , p) → isOfHLevelRespectEquiv 2 (invEquiv p) isSetFin)

isPropIsFinSet : isProp (isFinSet A)
isPropIsFinSet = isPropPropTrunc

-- the type of finite sets/propositions

FinSet : (ℓ : Level) → Type (ℓ-suc ℓ)
FinSet ℓ = TypeWithStr _ isFinSet

FinProp : (ℓ : Level) → Type (ℓ-suc ℓ)
FinProp ℓ = Σ[ P ∈ FinSet ℓ ] isProp (P .fst)

-- equality between finite sets/propositions

FinSet≡ : (X Y : FinSet ℓ) → (X .fst ≡ Y .fst) ≃ (X ≡ Y)
FinSet≡ _ _ = Σ≡PropEquiv (λ _ → isPropIsFinSet)

FinProp≡ : (X Y : FinProp ℓ) → (X .fst .fst ≡ Y .fst .fst) ≃ (X ≡ Y)
FinProp≡ X Y = compEquiv (FinSet≡ (X .fst) (Y .fst)) (Σ≡PropEquiv (λ _ → isPropIsProp))

-- hlevels of FinSet and FinProp

isGroupoidFinSet : isGroupoid (FinSet ℓ)
isGroupoidFinSet X Y =
  isOfHLevelRespectEquiv 2 (FinSet≡ X Y)
    (isOfHLevel≡ 2 (isFinSet→isSet (X .snd)) (isFinSet→isSet (Y .snd)))

isSetFinProp : isSet (FinProp ℓ)
isSetFinProp X Y =
  isOfHLevelRespectEquiv 1 (FinProp≡ X Y) (isOfHLevel≡ 1 (X .snd) (Y .snd))
