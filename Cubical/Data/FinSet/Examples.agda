{-

Computable stuff

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.Fin
open import Cubical.Data.FinSet hiding (isFinSetΣ)
open import Cubical.Data.FinSet.Properties

-- some computable functions

card+ : ℕ → ℕ → ℕ
card+ m n = card (Fin m ⊎ Fin n , isFinSet⊎ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card× : ℕ → ℕ → ℕ
card× m n = card (Fin m × Fin n , isFinSet× (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card→ : ℕ → ℕ → ℕ
card→ m n = card ((Fin m → Fin n) , isFinSet→ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

card≃ : ℕ → ℕ → ℕ
card≃ m n = card ((Fin m ≃ Fin n) , isFinSet≃ (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardInj : ℕ → ℕ → ℕ
cardInj m n = card (Injection (Fin m) (Fin n) , isFinSetInjection (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardSurj : ℕ → ℕ → ℕ
cardSurj m n = card (Surjection (Fin m) (Fin n) , isFinSetSurjection (Fin m , isFinSetFin) (Fin n , isFinSetFin))

cardBij : ℕ → ℕ → ℕ
cardBij m n = card (Bijection (Fin m) (Fin n) , isFinSetBijection (Fin m , isFinSetFin) (Fin n , isFinSetFin))

-- explicit numbers

s2 : card≃ 2 2 ≡ 2
s2 = refl

s3 : card≃ 3 3 ≡ 6
s3 = refl
