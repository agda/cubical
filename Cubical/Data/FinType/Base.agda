{-

Finite Types

This file formalize the notion of Rijke finite type,
which is a direct generalization of Bishop finite set.
Basically, a type is (Rijke) n-finite if its i-th order
homotopy groups πᵢ are Bishop finite for i ≤ n.

Referrences:
  https://github.com/EgbertRijke/OEIS-A000001

-}

module Cubical.Data.FinType.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

private
  variable
    ℓ ℓ' : Level
    n : ℕ
    X : Type ℓ

-- the (Rijke) finite type

isFinType : (n : ℕ) → Type ℓ → Type ℓ
isFinType 0 X = isFinSet ∥ X ∥₂
isFinType (suc n) X = (isFinType 0 X) × ((a b : X) → isFinType n (a ≡ b))

isPropIsFinType : isProp (isFinType n X)
isPropIsFinType {n = 0} = isPropIsFinSet
isPropIsFinType {n = suc n} = isProp× isPropIsFinSet (isPropΠ2 (λ _ _ → isPropIsFinType {n = n}))

-- the type of finite types

FinType : (ℓ : Level)(n : ℕ) → Type (ℓ-suc ℓ)
FinType ℓ n = TypeWithStr ℓ (isFinType n)

-- basic numerical implications

isFinTypeSuc→isFinType : isFinType (suc n) X → isFinType n X
isFinTypeSuc→isFinType {n = 0} p = p .fst
isFinTypeSuc→isFinType {n = suc n} p .fst = p .fst
isFinTypeSuc→isFinType {n = suc n} p .snd a b = isFinTypeSuc→isFinType {n = n} (p .snd a b)

isFinType→isFinType0 : isFinType n X → isFinType 0 X
isFinType→isFinType0 {n = 0} p = p
isFinType→isFinType0 {n = suc n} p = p .fst

isFinTypeSuc→isFinType1 : isFinType (suc n) X → isFinType 1 X
isFinTypeSuc→isFinType1 {n = 0} p = p
isFinTypeSuc→isFinType1 {n = suc n} p .fst = p .fst
isFinTypeSuc→isFinType1 {n = suc n} p .snd a b = isFinType→isFinType0 {n = suc n} (p .snd a b)
