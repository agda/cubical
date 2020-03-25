{-

An simpler definition of truncation from n ≥ -1

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.FromNegOne.Base where

open import Cubical.Data.NatMinusOne renaming (suc₋₁ to suc)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn

data  ∥_∥_ {ℓ} (A : Type ℓ) (n : ℕ₋₁) : Type ℓ where
  ∣_∣ : A  → ∥ A ∥ n
  hub : (f : S (suc n) → ∥ A ∥ n) → ∥ A ∥ n
  spoke : (f : S (suc n) → ∥ A ∥ n) (x : S (suc n)) → hub f ≡ f x
