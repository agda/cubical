{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Experiments.NatMinusTwo.ToNatMinusOne where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.NatMinusOne as ℕ₋₁ using (ℕ₋₁)
open import Cubical.Experiments.NatMinusTwo.Base as ℕ₋₂ using (ℕ₋₂; -2+_)

-- Conversions to/from ℕ₋₁

-1+_ : ℕ₋₁ → ℕ₋₂
-1+ (ℕ₋₁.-1+ n) = -2+ n

1+_ : ℕ₋₂ → ℕ₋₁
1+ (-2+ n) = ℕ₋₁.-1+ n

ℕ₋₁→ℕ₋₂ : ℕ₋₁ → ℕ₋₂
ℕ₋₁→ℕ₋₂ (ℕ₋₁.-1+ n) = ℕ₋₂.-1+ n

-- Properties

-1+Path : ℕ₋₁ ≡ ℕ₋₂
-1+Path = isoToPath (iso -1+_ 1+_ (λ _ → refl) (λ _ → refl))
