module Cubical.Tactics.CommRingSolver.RationalsExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals hiding (_+_ ; _·_ ; _-_; -_)

open import Cubical.Data.Nat using (ℕ; suc; zero)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolver.Reflection

-- imports to obtain `fromNat` instances
import Cubical.Data.NatPlusOne
import Cubical.Data.Int


private
  variable
    ℓ ℓ' : Level

open ℚRingSolver

module TestWithℤ (v : ℕ → ℚ) where
 open CommRingStr (ℚCommRing .snd)

 _ : 5 · v 0 + 190 · v 1 +  6 · v 0 ≡ (v 1 · 100 + 11 · v 0 +  v 1 · 90)
 _ = ℚ!


 e0 : ∀ (x y z : ℚ)  → 4 · (([ 1 / 6 ] · x) + (x · [ 1 / 3 ])) + y ≡ x + y + x
 e0 _ _ _ = ℚ!


 ex13 : (x y : ℚ) → (x · y) · 1r ≡ (y · x) · 1r
 ex13 x y = ℚ!
