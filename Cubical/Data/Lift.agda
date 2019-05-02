{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Lift where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat

liftLevel : ∀ {ℓ ℓ'} (n : ℕ) {A : Type ℓ} → isOfHLevel n A → isOfHLevel n (Lift {j = ℓ'} A)
liftLevel n = retractIsOfHLevel n lower lift λ _ → refl
