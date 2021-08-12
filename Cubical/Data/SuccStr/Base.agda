{-# OPTIONS --safe #-}
{-
  Successor structures for spectra, chain complexes and fiber sequences.
  This is an idea from Floris van Doorn's phd thesis.
-}
module Cubical.Data.SuccStr.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int
open import Cubical.Data.Nat

private
  variable
    ℓ ℓ′ : Level

record SuccStr (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor succstr
  field
    Index : Type ℓ
    succ : Index → Index

TypeSeq : (ℓ″ : Level) (S : SuccStr ℓ) → Type _
TypeSeq ℓ″ S = let open SuccStr S
               in Σ[ seq ∈ (Index → Type ℓ″) ] ((i : Index) → (seq i) → (seq (succ i)))

open SuccStr

ℤ+ : SuccStr ℓ-zero
ℤ+ .Index = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .Index = ℕ
ℕ+ .succ = suc
