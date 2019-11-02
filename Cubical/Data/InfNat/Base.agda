{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.Data.InfNat.Base where

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Core.Primitives

data ℕ+∞ : Type₀ where
  ∞ : ℕ+∞
  fin : ℕ → ℕ+∞

suc : ℕ+∞ → ℕ+∞
suc ∞ = ∞
suc (fin n) = fin (ℕ.suc n)

zero : ℕ+∞
zero = fin ℕ.zero

caseInfNat : ∀ {ℓ} → {A : Type ℓ} → (aF aI : A) → ℕ+∞ → A
caseInfNat aF aI (fin n) = aF
caseInfNat aF aI ∞       = aI

infixl 6 _+_ _ℕ+_
_ℕ+_ : ℕ → ℕ+∞ → ℕ+∞
_ℕ+_ n = ℕ.iter n suc

_+_ : ℕ+∞ → ℕ+∞ → ℕ+∞
∞     + m = ∞
fin n + m = n ℕ+ m
