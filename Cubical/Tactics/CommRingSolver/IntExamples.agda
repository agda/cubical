module Cubical.Tactics.CommRingSolver.IntExamples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; _-_; -_)
open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ; suc; zero)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Int
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolver.Reflection
-- open import Cubical.Tactics.CommRingSolverFast.RawAlgebra using (scalar)

private
  variable
    ℓ ℓ' : Level

-- module TestErrors (R : CommRing ℓ) where
--   open CommRingStr (snd R)

--   {-
--     The following should give an type checking error,
--     making the user aware that the problem is, that 'Type₀'
--     is not a CommRing.
--   -}
--   {-
--   _ : 0r ≡ 0r
--   _ = solve Type₀
--   -}

open FastℤRingSolver

module TestWithℤ (v : ℕ → ℤ) where
 open CommRingStr (ℤCommRing .snd)

 _ : 5 · v 0 + 190 · v 1 +  6 · v 0 ≡ (v 1 · 100 + 11 · v 0 +  v 1 · 90)
 _ = ℤ!

 _ : 5 · v 0 + (negsuc (1899999)) · v 1 +  6 · v 0 ≡ (v 1 · (- 1000000) + 11 · v 0 +  v 1 · (- 900000))
 _ = ℤ!


 ex13 : (x y : ℤ) → (x · y) · 1r ≡ (y · x) · 1r 
 ex13 x y = ℤ!

 ex0 : (a b : fst ℤCommRing) → a + b ≡ b + a
 ex0 a b = ℤ!
