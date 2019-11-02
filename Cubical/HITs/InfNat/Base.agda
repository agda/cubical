{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.HITs.InfNat.Base where

open import Cubical.Core.Everything
open import Cubical.Data.Maybe
open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

data ℕ+∞ : Type₀ where
  zero : ℕ+∞
  suc : ℕ+∞ → ℕ+∞
  ∞ : ℕ+∞
  suc-inf : ∞ ≡ suc ∞
