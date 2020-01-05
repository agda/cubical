{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Base where

open import Cubical.Core.Primitives

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)
open import Cubical.Data.Unit.Base public

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

ℕ-induction : ∀ {ℓ} {A : ℕ → Type ℓ}
            → A 0
            → ((n : ℕ) → A n → A (suc n))
            → (n : ℕ) → A n
ℕ-induction a₀ _ zero = a₀
ℕ-induction a₀ f (suc n) = f n ((ℕ-induction a₀ f n))
