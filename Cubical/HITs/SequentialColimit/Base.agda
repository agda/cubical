{-# OPTIONS --safe #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

record Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    space : ℕ → Type ℓ
    map : {n : ℕ} → space n → space (1 + n)

open Sequence

data Lim→ (X : Sequence ℓ) : Type ℓ where
  inl : {n : ℕ} → X .space n → Lim→ X
  push : {n : ℕ}(x : X .space n) → inl x ≡ inl (X .map x)
