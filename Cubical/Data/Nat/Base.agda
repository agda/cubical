{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Base where

open import Cubical.Core.Primitives

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

-- Allows for (constrained) natural number and negative integer
--  literals for any type (e.g. ℕ, ℕ₋₁, ℕ₋₂, Int)
open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)
open import Cubical.Data.Unit.Base public

-- Natural number literals for ℕ
instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = record { Constraint = λ _ → Unit ; fromNat = λ n → n }

predℕ : ℕ → ℕ
predℕ zero    = 0
predℕ (suc n) = n

caseNat : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS 0       = a0
caseNat a0 aS (suc n) = aS

doubleℕ : ℕ → ℕ
doubleℕ 0 = 0
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ 0 m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

-- iterate
iter : ∀ {ℓ} {A : Type ℓ} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)

elim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → A 0
  → ((n : ℕ) → A n → A (suc n))
  → (n : ℕ) → A n
elim a₀ _ zero = a₀
elim a₀ f (suc n) = f n (elim a₀ f n)
