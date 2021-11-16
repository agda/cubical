{-

Definitions to reduce problems about FinSet to SumFin

-}
{-# OPTIONS --safe #-}

module Cubical.Data.FinSet.SumFinReduction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.SumFin renaming (Fin to SumFin)

private
  variable
    ℓ ℓ' : Level

_⋆_ = compEquiv

infixr 30 _⋆_

≃Fin : Type ℓ → Type ℓ
≃Fin A = Σ[ n ∈ ℕ ] A ≃ Fin n

≃SumFin : Type ℓ → Type ℓ
≃SumFin A = Σ[ n ∈ ℕ ] A ≃ SumFin n

≃Fin→SumFin : {X : Type ℓ} → ≃Fin X → ≃SumFin X
≃Fin→SumFin (n , e) = n , compEquiv e (invEquiv (SumFin≃Fin _))

≃SumFin→Fin : {X : Type ℓ} → ≃SumFin X → ≃Fin X
≃SumFin→Fin (n , e) = n , compEquiv e (SumFin≃Fin _)

transpFamily : {X : Type ℓ}{Y : X → Type ℓ'}
  → ((n , e) : ≃SumFin X) → (x : X) → Y x ≃ Y (invEq e (e .fst x))
transpFamily {X = X} {Y = Y} (n , e) x = pathToEquiv (λ i → Y (retEq e x (~ i)))
