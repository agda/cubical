{-

This file contains the counting number of finite sets with structure.

https://github.com/EgbertRijke/OEIS-A000001

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.CountingFiniteStructure where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.FinType
open import Cubical.Data.FinSet.FiniteStructure

private
  variable
    ℓ : Level

-- convenient abbreviation

isFinStrCard : (S : FinSet ℓ-zero → FinSet ℓ) (n : ℕ) → isFinType 0 (FinSetWithStrOfCard ℓ-zero S n)
isFinStrCard S n = isFinTypeFinSetWithStrOfCard ℓ-zero S n

-- structure that is no structure

TrivialStr : FinSet ℓ → FinSet ℓ
TrivialStr _ = 𝟙

-- identity structure

IdentityStr : FinSet ℓ → FinSet ℓ
IdentityStr X = X

-- finite semi-groups

FinSemiGroupStr : FinSet ℓ → FinSet ℓ
FinSemiGroupStr X .fst =
  Σ[ p ∈ (X .fst → X .fst → X .fst) ] ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
FinSemiGroupStr X .snd =
  isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X))
    (λ p → _ , isFinSetΠ3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isFinSet≡ X _ _))

FinSemiGroupOfCard : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
FinSemiGroupOfCard ℓ n = FinSetWithStrOfCard ℓ FinSemiGroupStr n

isFinSemiGroupOfCard : (ℓ : Level) (n : ℕ) → isFinType 0 (FinSemiGroupOfCard ℓ n)
isFinSemiGroupOfCard ℓ n = isFinTypeFinSetWithStrOfCard _ FinSemiGroupStr _

-- two rather trivial numbers
-- but the computation is essentially not that trivial
-- this one can be computed in half-a-minute
g : ℕ
g = card (_ , isFinStrCard TrivialStr 2)

-- this is already hard to compute
-- don't know if anyone's computer give the final result
f : ℕ
f = card (_ , isFinStrCard IdentityStr 2)

-- the number of finite semi-groups with cardinal 2
-- it should be 5
-- would you like to try?
n2 : ℕ
n2 = card (_ , isFinStrCard FinSemiGroupStr 2)
