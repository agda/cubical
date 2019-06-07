{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Sn

-- note: only works when n is non-zero
data  ∥_∥_ {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  ∣_∣ : A  → ∥ A ∥ n
  top : (f : S n → ∥ A ∥ n) → ∥ A ∥ n
  rays : (f : S n → ∥ A ∥ n) (x : S n) → top f ≡ f x
