{-# OPTIONS --safe #-}
module Cubical.Data.Sequence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Fin

private
  variable
    ℓ ℓ' ℓ'' : Level

record Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor sequence
  field
    obj : ℕ → Type ℓ
    map : {n : ℕ} → obj n → obj (1 + n)

record SequenceMap (C : Sequence ℓ) (D : Sequence ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor sequencemap
  field
    map : (n : ℕ) → Sequence.obj C n → Sequence.obj D n
    comm : (n : ℕ) (x : Sequence.obj C n)
      → Sequence.map D (map n x) ≡ map (suc n) (Sequence.map C x)

converges : ∀ {ℓ} → Sequence ℓ → (n : ℕ) → Type ℓ
converges seq n = (k : ℕ) → isEquiv (Sequence.map seq {n = k + n})

finiteSequence : (ℓ : Level) (m : ℕ) → Type (ℓ-suc ℓ)
finiteSequence ℓ m = Σ[ S ∈ Sequence ℓ ] converges S m
