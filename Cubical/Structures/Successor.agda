{-# OPTIONS --safe #-}
{-
  Successor structures for spectra, chain complexes and fiber sequences.
  This is an idea from Floris van Doorn's phd thesis.
-}
module Cubical.Structures.Successor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Fin

private
  variable
    ℓ : Level

record SuccStr (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Index : Type ℓ
    succ : Index → Index

open SuccStr

ℤ+ : SuccStr ℓ-zero
ℤ+ .Index = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .Index = ℕ
ℕ+ .succ = suc

Fin+ : (n : ℕ) → SuccStr ℓ-zero
Fin+ n .Index = Fin n
Fin+ n .succ (x , zero , p) = x , zero , p
Fin+ n .succ (x , suc diff , p) = suc x , diff , +-suc diff (suc x) ∙ p
