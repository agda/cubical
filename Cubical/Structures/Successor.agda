{-# OPTIONS --safe #-}
{-
  Successor structures for spectra, chain complexes and fiber sequences.
  This is an idea from Floris van Doorn's phd thesis.
-}
module Cubical.Structures.Successor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

record SuccStr (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    S : Type ℓ
    succ : S → S

open SuccStr

ℤ+ : SuccStr ℓ-zero
ℤ+ .S = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .S = ℕ
ℕ+ .succ = suc
