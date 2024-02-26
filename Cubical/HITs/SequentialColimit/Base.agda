{-# OPTIONS --safe #-}
module Cubical.HITs.SequentialColimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Sequence


private
  variable
    ℓ ℓ' : Level

open Sequence

data SeqColim (X : Sequence ℓ) : Type ℓ where
  incl : {n : ℕ} → X .obj n → SeqColim X
  push : {n : ℕ} (x : X .obj n) → incl x ≡ incl (X .map x)

realiseSequenceMap : {C : Sequence ℓ} {D : Sequence ℓ'}
  → SequenceMap C D → SeqColim C → SeqColim D
realiseSequenceMap record { map = map ; comm = comm } (incl x) = incl (map _ x)
realiseSequenceMap record { map = map ; comm = comm } (push {n = n} x i) =
  (push (map n x) ∙ λ i → incl (comm n x i)) i
