{-# OPTIONS --safe #-}
module Cubical.HITs.Rationals.HITQ.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import Cubical.Data.Int

open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma


-- ℚ as a higher inductive type

data ℚ : Type₀ where
  con : (u : ℤ) (a : ℤ) → ¬ (a ≡ pos 0) → ℚ
  path : ∀ u a v b {p q} → (u · b) ≡ (v · a) → con u a p ≡ con v b q
  trunc : isSet ℚ

[_] : ℤ × ℕ₊₁ → ℚ
[ a , 1+ b ] = con a (pos (suc b)) (ℕ.snotz ∘ cong abs)


-- Natural number and negative integer literals for ℚ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℚ : HasFromNat ℚ
  fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n , 1 ] }

instance
  fromNegℚ : HasFromNeg ℚ
  fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n , 1 ] }
