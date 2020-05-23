{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusTwo.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty

record ℕ₋₂ : Type₀ where
  constructor -2+_
  field
    n : ℕ

pattern neg2 = -2+ zero
pattern neg1 = -2+ (suc zero)
pattern ℕ→ℕ₋₂ n = -2+ (suc (suc n))
pattern -1+_ n = -2+ (suc n)

2+_ : ℕ₋₂ → ℕ
2+ (-2+ n) = n

pred₋₂ : ℕ₋₂ → ℕ₋₂
pred₋₂ neg2 = neg2
pred₋₂ neg1 = neg2
pred₋₂ (ℕ→ℕ₋₂ zero) = neg1
pred₋₂ (ℕ→ℕ₋₂ (suc n)) = (ℕ→ℕ₋₂ n)

suc₋₂ : ℕ₋₂ → ℕ₋₂
suc₋₂ (-2+ n) = -2+ (suc n)

-- Natural number and negative integer literals for ℕ₋₂

open import Cubical.Data.Nat.Literals public

instance
  fromNatℕ₋₂ : HasFromNat ℕ₋₂
  fromNatℕ₋₂ = record { Constraint = λ _ → Unit ; fromNat = ℕ→ℕ₋₂ }

instance
  fromNegℕ₋₂ : HasFromNeg ℕ₋₂
  fromNegℕ₋₂ = record { Constraint = λ { (suc (suc (suc _))) → ⊥ ; _ → Unit }
                       ; fromNeg = λ { zero → 0 ; (suc zero) → neg1 ; (suc (suc zero)) → neg2 } }
