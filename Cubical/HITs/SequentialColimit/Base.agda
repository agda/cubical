{-# OPTIONS --safe #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

record Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    obj : ℕ → Type ℓ
    map : {n : ℕ} → obj n → obj (1 + n)

open Sequence

data SeqColim (X : Sequence ℓ) : Type ℓ where
  incl : {n : ℕ} → X .obj n → SeqColim X
  push : {n : ℕ} (x : X .obj n) → incl x ≡ incl (X .map x)
