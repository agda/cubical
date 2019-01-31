{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Nat where

open import Cubical.Core.Primitives
open import Cubical.Core.Prelude

open import Cubical.Basics.NTypes

open import Cubical.Data.Empty

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

predℕ : ℕ → ℕ
predℕ zero    = 0
predℕ (suc n) = n

caseNat : ∀{l} → {A : Set l} → (a0 aS : A) → ℕ → A
caseNat a0 aS 0       = a0
caseNat a0 aS (suc n) = aS

znots : {n : ℕ} → ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : {n : ℕ} → ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

doubleℕ : ℕ → ℕ
doubleℕ 0 = 0
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ 0 m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

private
  -- 1024 = 2^8 * 2^2 = 2^10
  n1024 : ℕ
  n1024 = doublesℕ 8 4

-- iterate
iter : ∀ {ℓ} {A : Set ℓ} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)

discreteℕ : discrete ℕ
discreteℕ zero zero = inl refl
discreteℕ zero (suc n) = inr znots
discreteℕ (suc m) zero = inr snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | inl p = inl (cong suc p)
... | inr p = inr (λ x → p (injSuc x))

isSetℕ : isSet ℕ
isSetℕ = discrete→isSet discreteℕ
