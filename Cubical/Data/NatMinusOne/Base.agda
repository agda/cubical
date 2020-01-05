{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusOne.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty

data ℕ₋₁ : Set where
  neg1 : ℕ₋₁
  suc  : (n : ℕ₋₁) → ℕ₋₁

1+_ : ℕ₋₁ → ℕ
1+ neg1 = zero
1+ suc n = suc (1+ n)

-1+_ : ℕ → ℕ₋₁
-1+ zero = neg1
-1+ suc n = suc (-1+ n)

ℕ→ℕ₋₁ : ℕ → ℕ₋₁
ℕ→ℕ₋₁ n = suc (-1+ n)

_+₋₁_ : ℕ → ℕ₋₁ → ℕ₋₁
0 +₋₁ n = n
suc m +₋₁ n = suc (m +₋₁ n)

instance
  fromNatℕ₋₁ : HasFromNat ℕ₋₁
  fromNatℕ₋₁ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→ℕ₋₁ n }

instance
  fromNegℕ₋₁ : HasFromNeg ℕ₋₁
  fromNegℕ₋₁ = record { Constraint = λ { (suc (suc _)) → ⊥ ; _ → Unit }
                      ; fromNeg = λ { zero → suc neg1 ; _ → neg1 } }
