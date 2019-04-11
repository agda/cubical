{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Rational.Base where

open import Cubical.Relation.Nullary
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.HITs.HitInt
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit

data ℚ : Type₀ where
  con : (u : ℤ) (a : ℤ) → ¬ (a ≡ pos 0) → ℚ
  path : ∀ u a v b {p q} → (u *ℤ b) ≡ (v *ℤ a) → con u a p ≡ con v b q
  trunc : isSet ℚ

int : ℤ → ℚ
int z = con z (pos 1) \ p → snotz (cong abs p)
