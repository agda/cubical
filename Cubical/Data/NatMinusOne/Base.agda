{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.NatMinusOne.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat

data ℕ₋₁ : Set where
  neg1 : ℕ₋₁
  suc  : (n : ℕ₋₁) → ℕ₋₁

_+₋₁_ : ℕ → ℕ₋₁ → ℕ₋₁
0 +₋₁ n = n
suc m +₋₁ n = suc (m +₋₁ n)

ℕ→ℕ₋₁ : ℕ → ℕ₋₁
ℕ→ℕ₋₁ n = suc (n +₋₁ neg1)

1+_ : ℕ₋₁ → ℕ
1+ neg1 = zero
1+ suc n = suc (1+ n)

