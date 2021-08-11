{-# OPTIONS --safe #-}
{-
  This uses ideas from Floris van Doorn's phd thesis.
-}
module Cubical.Homotopy.Prespectrum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed

open import Cubical.Structures.Successor

open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ ℓ′ : Level

record Prespectrum {S : SuccStr ℓ} : Type (ℓ-max (ℓ-suc ℓ′) ℓ) where
  open SuccStr S
  field
    Space : Index → Pointed ℓ′
    map : (i : Index) → (Space i →∙ Ω (Space (succ i)))
