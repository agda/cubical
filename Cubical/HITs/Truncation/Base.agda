{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Data.NatMinusOne
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn

data  ∥_∥_ {ℓ} (A : Type ℓ) (n : ℕ₋₁) : Type ℓ where
  ∣_∣ : A  → ∥ A ∥ n
  hub : (f : S (1+ n) → ∥ A ∥ n) → ∥ A ∥ n
  spoke : (f : S (1+ n) → ∥ A ∥ n) (x : S (1+ n)) → hub f ≡ f x

