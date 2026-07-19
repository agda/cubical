module Cubical.Data.FinData.FiniteChoice where
{-
  Finite choice for 'Fin n'
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Sigma
open import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat as ℕ

import Cubical.Data.SumFin.Properties as SumFin
import Cubical.Data.Fin as Fin
import Cubical.Data.FinSet.FiniteChoice as FinSet

private variable
   ℓ : Level

choice : {n : ℕ} (T : Fin n → Type ℓ) → ((x : Fin n) → ∥ T x ∥₁) → ∥ ((x : Fin n) → T x) ∥₁
choice {n = n} T t =
  FinSet.choice (Fin n , n , ∣ compEquiv (Fin.FinData≃Fin n) (invEquiv (SumFin.SumFin≃Fin n)) ∣₁) T t
