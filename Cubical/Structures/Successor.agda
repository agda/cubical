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

SuccStr : {A : Type ℓ} → Type _
SuccStr {A = A} = A → A

ℤ+ : SuccStr
ℤ+ = sucℤ

ℕ+ : SuccStr
ℕ+ = suc
