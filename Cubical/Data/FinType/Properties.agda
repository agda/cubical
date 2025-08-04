{-

This file contains:
- Some basic properties of Rijke finite types.

-}

module Cubical.Data.FinType.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

open import Cubical.HITs.SetTruncation

open import Cubical.Data.Nat
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinType.Base

private
  variable
    ℓ ℓ' : Level
    n : ℕ
    X : Type ℓ
    Y : Type ℓ'

EquivPresIsFinType : (n : ℕ) → X ≃ Y → isFinType n X → isFinType n Y
EquivPresIsFinType 0 e = EquivPresIsFinSet (isoToEquiv (setTruncIso (equivToIso e)))
EquivPresIsFinType (suc n) e (p , q) .fst = EquivPresIsFinType 0 e p
EquivPresIsFinType (suc n) e (p , q) .snd a b =
  EquivPresIsFinType n (invEquiv (congEquiv (invEquiv e))) (q _ _)

isFinSet→isFinType : (n : ℕ) → isFinSet X → isFinType n X
isFinSet→isFinType 0 p = EquivPresIsFinSet (invEquiv (setTruncIdempotent≃ (isFinSet→isSet p))) p
isFinSet→isFinType (suc n) p .fst = isFinSet→isFinType 0 p
isFinSet→isFinType (suc n) p .snd a b = isFinSet→isFinType n (isFinSet≡ (_ , p) _ _)

isPathConnected→isFinType0 : isContr ∥ X ∥₂ → isFinType 0 X
isPathConnected→isFinType0 p = isContr→isFinSet p
