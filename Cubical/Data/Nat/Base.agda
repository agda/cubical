{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Base where

open import Cubical.Core.Primitives

open import Agda.Builtin.Nat public
  using (zero; suc; _+_)
  renaming (Nat to ℕ; _-_ to _∸_; _*_ to _·_)

open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Bool.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Empty.Base hiding (elim)
open import Cubical.Data.Unit.Base

predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n

caseNat : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS zero    = a0
caseNat a0 aS (suc n) = aS

doubleℕ : ℕ → ℕ
doubleℕ zero = zero
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n · m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ zero m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

-- iterate
iter : ∀ {ℓ} {A : Type ℓ} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)

elim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → A zero
  → ((n : ℕ) → A n → A (suc n))
  → (n : ℕ) → A n
elim a₀ _ zero = a₀
elim a₀ f (suc n) = f n (elim a₀ f n)

isEven isOdd : ℕ → Bool
isEven zero = true
isEven (suc n) = isOdd n
isOdd zero = false
isOdd (suc n) = isEven n

--Typed version
private
  toType : Bool → Type
  toType false = ⊥
  toType true = Unit

isEvenT : ℕ → Type
isEvenT n = toType (isEven n)

isOddT : ℕ → Type
isOddT n = isEvenT (suc n)

isZero : ℕ → Bool
isZero zero = true
isZero (suc n) = false

-- exponential

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m · m ^ n
