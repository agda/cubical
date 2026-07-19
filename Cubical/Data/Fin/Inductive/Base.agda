
-- Definition of Fin n in terms of the inductively defined <

module Cubical.Data.Fin.Inductive.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

-- Fin defined using <ᵗ
Fin : (n : ℕ) → Type
Fin n = Σ[ m ∈ ℕ ] (m <ᵗ n)

fsuc : {n : ℕ} → Fin n → Fin (suc n)
fst (fsuc {n = n} (x , p)) = suc x
snd (fsuc {n = suc n} (x , p)) = p

injectSuc : {n : ℕ} → Fin n → Fin (suc n)
fst (injectSuc {n = n} (x , p)) = x
snd (injectSuc {n = suc n} (x , p)) = <ᵗ-trans-suc {n = x} p

flast : {m : ℕ} → Fin (suc m)
fst (flast {m = m}) = m
snd (flast {m = m}) = <ᵗsucm {m = m}

fzero : {m : ℕ} → Fin (suc m)
fzero = 0 , tt

fone : ∀ {m} → Fin (suc (suc m))
fone {m} = suc zero , tt

-- Sums
sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ}
  (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
sumFinGen {n = zero} _+_ 0A f = 0A
sumFinGen {n = suc n} _+_ 0A f =
  f flast + (sumFinGen {n = n}) _+_ 0A (f ∘ injectSuc)
