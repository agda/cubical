{-

  Importing and re-exporting this module allows for (constrained) natural number
   and negative integer literals for any type (e.g. Int, ℕ₋₁, ℕ₋₂, ℕ₊₁).

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Data.Nat.Literals where

open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)
open import Cubical.Data.Unit.Base public

-- Natural number literals for ℕ

open import Agda.Builtin.Nat renaming (Nat to ℕ)

instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = record { Constraint = λ _ → Unit ; fromNat = λ n → n }
