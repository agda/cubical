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
    index : Type ℓ
    succ : index → index

private
  variable
    S : SuccStr ℓ

open SuccStr

TypeSeq : (ℓ″ : Level) (S : SuccStr ℓ) → Type _
TypeSeq ℓ″ S = Σ[ seq ∈ (index S → Type ℓ″) ] ((i : index S) → (seq i) → (seq (succ S i)))

ShiftedSeq : (s : TypeSeq ℓ S) (n : ℕ)
             → TypeSeq ℓ S
ShiftedSeq s zero = s
ShiftedSeq {S = S} s (suc n) = let seq = fst (ShiftedSeq s n)
                                   map = snd (ShiftedSeq s n)
                               in (λ i → seq (succ S i)) , λ i →  (λ x → map (succ S i) x)

ΣSeq : (s : TypeSeq ℓ S) → Type _
ΣSeq {S = S} s = Σ[ i ∈ (index S) ] (fst s i)

open SuccStr

TimesSucc : (n : ℕ) (S : SuccStr ℓ) (i : index S) → index S
TimesSucc zero S i = i
TimesSucc (suc n) S i = succ S (TimesSucc n S i)

TimesSeqOp : (n : ℕ) (s : TypeSeq ℓ S) {i : index S}
              → (x : fst s i) → fst s (TimesSucc n S i)
TimesSeqOp zero s x = x
TimesSeqOp (suc n) s x = snd s _ (TimesSeqOp n s x)

ℤ+ : SuccStr ℓ-zero
ℤ+ .index = ℤ
ℤ+ .succ = sucℤ

ℕ+ : SuccStr ℓ-zero
ℕ+ .index = ℕ
ℕ+ .succ = suc
