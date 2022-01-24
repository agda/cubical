{-

Computable stuff constructed from the Combinatorics of Finite Sets

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.Combinatorics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.Fin
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

-- some computable functions

-- this should be addtion
card+ : ℕ → ℕ → ℕ
card+ m n = card (Fin m ⊎ Fin n , isFinSet⊎ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- this should be multiplication
card× : ℕ → ℕ → ℕ
card× m n = card (Fin m × Fin n , isFinSet× (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- this should be exponential
card→ : ℕ → ℕ → ℕ
card→ m n = card ((Fin m → Fin n) , isFinSet→ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- this should be factorial or zero
card≃ : ℕ → ℕ → ℕ
card≃ m n = card ((Fin m ≃ Fin n) , isFinSet≃ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- this should be binomial coeffient
card↪ : ℕ → ℕ → ℕ
card↪ m n = card ((Fin m ↪ Fin n) , isFinSet↪ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- this should be something that I don't know the name
card↠ : ℕ → ℕ → ℕ
card↠ m n = card ((Fin m ↠ Fin n) , isFinSet↠ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- explicit numbers

s2 : card≃ 2 2 ≡ 2
s2 = refl

s3 : card≃ 3 3 ≡ 6
s3 = refl

c3,2 : card↪ 2 3 ≡ 6
c3,2 = refl
