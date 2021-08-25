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

private
  variable
    S : SuccStr ℓ

open SuccStr

TypeSeq : (ℓ″ : Level) (S : SuccStr ℓ) → Type _
TypeSeq ℓ″ S = Σ[ seq ∈ (Index S → Type ℓ″) ] ((i : Index S) → (seq i) → (seq (succ S i)))

ShiftedSeq : (s : TypeSeq ℓ S) (n : ℕ)
             → TypeSeq ℓ S
ShiftedSeq s zero = s
ShiftedSeq {S = S} s (suc n) with ShiftedSeq s n
... | (seq , map) = (λ i → seq (succ S i)) , λ i →  (λ x → map (succ S i) x)

ΣSeq : (s : TypeSeq ℓ S) → Type _
ΣSeq {S = S} s = Σ[ i ∈ (Index S) ] (fst s i)

open SuccStr

ℤ+ : SuccStr ℓ-zero
ℤ+ .Index = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .Index = ℕ
ℕ+ .succ = suc
