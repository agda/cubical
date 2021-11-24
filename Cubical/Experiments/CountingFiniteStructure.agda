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

-- finite groups

FinGroupStr : FinSet ℓ → FinSet ℓ
FinGroupStr X .fst =
  Σ[ e ∈ X .fst ]
    Σ[ inv ∈ (X .fst → X .fst) ]
      Σ[ p ∈ (X .fst → X .fst → X .fst) ]
          ((x y z : X .fst) → p (p x y) z ≡ p x (p y z))
        × ((x : X .fst)
            → (p x e ≡ x) × (p e x ≡ x) × (p (inv x) x ≡ e) × (p x (inv x) ≡ e))
FinGroupStr X .snd =
  isFinSetΣ X (λ _ → _ ,
    isFinSetΣ (_ , isFinSetΠ X (λ _ → X)) (λ _ → _ ,
      isFinSetΣ (_ , isFinSetΠ2 X (λ _ → X) (λ _ _ → X)) (λ _ → _ ,
        isFinSet× (_ , isFinSetΠ3 X (λ _ → X) (λ _ _ → X) (λ _ _ _ → _ , isFinSet≡ X _ _)) (_ ,
          isFinSetΠ X (λ _ → _ ,
            isFinSet× (_ , isFinSet≡ X _ _) (_ ,
              isFinSet× (_ , isFinSet≡ X _ _) (_ ,
                isFinSet× (_ , isFinSet≡ X _ _) (_ , isFinSet≡ X _ _))))))))

-- two rather trivial numbers
-- but the computation is essentially not that trivial
-- this one can be computed in half-a-minute
a2 : ℕ
a2 = card (_ , isFinStrCard TrivialStr 2)

-- this is already hard to compute
-- it takes less than half-an-hour
b2 : ℕ
b2 = card (_ , isFinStrCard IdentityStr 2)

-- the number of finite semi-groups with cardinal 2
-- it should be 5
-- would you like to try?
n2 : ℕ
n2 = card (_ , isFinStrCard FinSemiGroupStr 2)

-- OEIS-A000001
-- I think you'd better not evaluate this function
numberOfFinGroups : ℕ → ℕ
numberOfFinGroups n = card (_ , isFinStrCard FinGroupStr n)
