{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.NatMinusOne using (ℕ₋₁; neg1; suc)
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Nullification
open import Cubical.HITs.Sn

∥_∥_ : ∀ {ℓ} → Type ℓ → ℕ₋₂ → Type ℓ
∥ A ∥ n = Null (S (1+ n)) A
