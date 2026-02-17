module Cubical.Tactics.CommRingSolver.IntAsRawRing where

open import Cubical.Data.Nat hiding (_+_; _·_)

open import Cubical.Data.Fast.Int
open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolver.RawRing


ℤAsRawRing : RawRing ℓ-zero
ℤAsRawRing = rawring ℤ (pos zero) (pos (suc zero)) _+_ _·_ (λ k → - k)
