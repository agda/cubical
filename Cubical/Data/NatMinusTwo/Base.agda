{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusTwo.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty

import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc; ℕ→ℕ₋₁)

data ℕ₋₂ : Set where
  neg2 : ℕ₋₂
  suc  : (n : ℕ₋₂) → ℕ₋₂

1+_ : ℕ₋₂ → ℕ₋₁
1+ neg2 = neg1
1+ suc n = suc (1+ n)

-1+_ : ℕ₋₁ → ℕ₋₂
-1+ neg1 = neg2
-1+ suc n = suc (-1+ n)

ℕ₋₁→ℕ₋₂ : ℕ₋₁ → ℕ₋₂
ℕ₋₁→ℕ₋₂ n = suc (-1+ n)

2+_ : ℕ₋₂ → ℕ
2+ n = ℕ₋₁.1+ (1+ n)

-2+_ : ℕ → ℕ₋₂
-2+ n = -1+ (ℕ₋₁.-1+ n)

ℕ→ℕ₋₂ : ℕ → ℕ₋₂
ℕ→ℕ₋₂ n = ℕ₋₁→ℕ₋₂ (ℕ→ℕ₋₁ n)

-- Natural number and negative integer literals for ℕ₋₂

instance
  fromNatℕ₋₂ : HasFromNat ℕ₋₂
  fromNatℕ₋₂ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→ℕ₋₂ n }

instance
  fromNegℕ₋₂ : HasFromNeg ℕ₋₂
  fromNegℕ₋₂ = record { Constraint = λ { (suc (suc (suc _))) → ⊥ ; _ → Unit }
                      ; fromNeg = λ { zero → suc (suc neg2) ; (suc zero) → suc neg2 ; _ → neg2 } }
