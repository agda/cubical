module Cubical.Tactics.CommRingSolverFast.IntAsRawRing where

open import Cubical.Data.Nat hiding (_+_; _·_)
open import Cubical.Data.Int.Fast


open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolverFast.RawRing

ℤAsRawRing : RawRing ℓ-zero
ℤAsRawRing = rawring ℤ (pos zero) (pos (suc zero)) _+_ _·_ (λ k → - k)

+Ridℤ : (k : ℤ) → (pos zero) + k ≡ k
+Ridℤ k = sym (pos0+ k)
