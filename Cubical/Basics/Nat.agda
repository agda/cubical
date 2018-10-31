{-# OPTIONS --cubical #-}
module Cubical.Basics.Nat where

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

doubleℕ : ℕ → ℕ
doubleℕ zero = zero
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ zero m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

-- 1024 = 2^8 * 2^2 = 2^10
n1024 : ℕ
n1024 = doublesℕ 8 4

-- iterate
iter : {A : Set} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)
