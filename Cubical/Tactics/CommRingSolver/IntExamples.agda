module Cubical.Tactics.CommRingSolver.IntExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; _-_; -_)

open import Cubical.Data.Nat using (ℕ; suc; zero)
import Cubical.Data.Nat as ℕ
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Fast.Int
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.FastIntPlus


private
  variable
    ℓ ℓ' : Level

open FastℤRingSolver

open CommRingStr (ℤCommRing .snd)

module TestWithℤ (v : ℕ → ℤ) (v' : ℕ → ℕ) where


 _ : 5 · v 0 + 190 · v 1 +  6 · v 0 ≡ (v 1 · 100 + 11 · v 0 +  v 1 · 90)
 _ = ℤ!

 _ : 5 · v 0 + (negsuc (1899999)) · v 1 +  6 · v 0 ≡ (v 1 · (- 1000000) + 11 · v 0 +  v 1 · (- 900000))
 _ = ℤ!


 ex13 : (x y : ℤ) → (x · y) · 1r ≡ (y · x) · 1r
 ex13 x y = ℤ!

 ex0 : (a b : fst ℤCommRing) → a + b ≡ b + a
 ex0 a b = ℤ!


 ex1 : (a b : fst ℤCommRing) → 2 + a + b + pos (v' 0 ℕ.+ v' 1) ≡ pos (suc (suc (v' 0))) + b + a + pos (v' 1)
 ex1 a b = ℤ!


module _ (z z₁ : ℤ) (n n₁ : ℕ) where
 _ : PathP (λ i → ℤ)
          (((pos 40 · z · pos (suc (n₁ ℕ.+ 0 ℕ.· suc n₁)) +
             pos 190 · z₁ · pos (suc (n ℕ.+ 59 ℕ.· suc n)))
            · pos (suc (n ℕ.+ 29 ℕ.· suc n))
            +
            pos 50 · z ·
            pos
            (suc
             (n₁ ℕ.+ 0 ℕ.· suc n₁ ℕ.+
              (n ℕ.+ 59 ℕ.· suc n) ℕ.· suc (n₁ ℕ.+ 0 ℕ.· suc n₁))))
           ·
           pos
           (suc
            (0 ℕ.+ n₁ ℕ.· 1 ℕ.+
             (n ℕ.+ 29 ℕ.· suc n ℕ.+
              (0 ℕ.+ n₁ ℕ.· 1) ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))
             ℕ.· suc (0 ℕ.+ n₁ ℕ.· 1))))
          (((z₁ · pos 100 · pos (suc (n ℕ.+ 29 ℕ.· suc n)) +
             pos 70 · z · pos (suc (0 ℕ.+ n₁ ℕ.· 1)))
            · pos (suc (0 ℕ.+ n₁ ℕ.· 1))
            +
            z₁ · pos 90 ·
            pos
            (suc
             (n ℕ.+ 29 ℕ.· suc n ℕ.+
              (0 ℕ.+ n₁ ℕ.· 1) ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))))
           ·
           pos
           (suc
            (n ℕ.+ 29 ℕ.· suc n ℕ.+
             (n₁ ℕ.+ 0 ℕ.· suc n₁ ℕ.+
              (n ℕ.+ 59 ℕ.· suc n) ℕ.· suc (n₁ ℕ.+ 0 ℕ.· suc n₁))
             ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))))
 _ = FastℤPlusRingSolver.solve!
