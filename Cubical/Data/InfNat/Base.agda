{-# OPTIONS --no-exact-split --safe #-}

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

infixl 6 _+_
_+_ : ℕ+∞ → ℕ+∞ → ℕ+∞
∞     + m     = ∞
fin n + ∞     = ∞
fin n + fin m = fin (n ℕ.+ m)

infixl 7 _·_
_·_ : ℕ+∞ → ℕ+∞ → ℕ+∞
fin m         · fin n         = fin (m ℕ.· n)
∞             · fin ℕ.zero    = zero
fin ℕ.zero    · ∞             = zero
∞             · ∞             = ∞
∞             · fin (ℕ.suc _) = ∞
fin (ℕ.suc _) · ∞             = ∞
