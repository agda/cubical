{-# OPTIONS --no-exact-split #-}

module Cubical.HITs.InfNat.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Maybe
open import Cubical.Data.Nat

data ℕ+∞ : Type₀ where
  zero : ℕ+∞
  suc : ℕ+∞ → ℕ+∞
  ∞ : ℕ+∞
  suc-inf : ∞ ≡ suc ∞
