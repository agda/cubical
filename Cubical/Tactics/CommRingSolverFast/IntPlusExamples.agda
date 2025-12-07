{-# OPTIONS --verbose ratSolverVars:20 #-}
module Cubical.Tactics.CommRingSolverFast.IntPlusExamples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Rationals.Fast
open import Cubical.Data.Int.Fast using (pos;negsuc)
import Cubical.Data.Int.Fast as ℤ
open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ; suc; zero)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Data.Rationals.Fast.Order
-- open import Cubical.Data.Rationals.Fast.Order.Properties
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolverFast.IntPlusReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
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

module _ (z z₁ : ℤ.ℤ) (n n₁ : ℕ) where
 _ : PathP (λ i → ℤ.ℤ)
          (((pos 40 ℤ.· z ℤ.· pos (suc (n₁ ℕ.+ 0 ℕ.· suc n₁)) ℤ.+
             pos 190 ℤ.· z₁ ℤ.· pos (suc (n ℕ.+ 59 ℕ.· suc n)))
            ℤ.· pos (suc (n ℕ.+ 29 ℕ.· suc n))
            ℤ.+
            pos 50 ℤ.· z ℤ.·
            pos
            (suc
             (n₁ ℕ.+ 0 ℕ.· suc n₁ ℕ.+
              (n ℕ.+ 59 ℕ.· suc n) ℕ.· suc (n₁ ℕ.+ 0 ℕ.· suc n₁))))
           ℤ.·
           pos
           (suc
            (0 ℕ.+ n₁ ℕ.· 1 ℕ.+
             (n ℕ.+ 29 ℕ.· suc n ℕ.+
              (0 ℕ.+ n₁ ℕ.· 1) ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))
             ℕ.· suc (0 ℕ.+ n₁ ℕ.· 1))))
          (((z₁ ℤ.· pos 100 ℤ.· pos (suc (n ℕ.+ 29 ℕ.· suc n)) ℤ.+
             pos 70 ℤ.· z ℤ.· pos (suc (0 ℕ.+ n₁ ℕ.· 1)))
            ℤ.· pos (suc (0 ℕ.+ n₁ ℕ.· 1))
            ℤ.+
            z₁ ℤ.· pos 90 ℤ.·
            pos
            (suc
             (n ℕ.+ 29 ℕ.· suc n ℕ.+
              (0 ℕ.+ n₁ ℕ.· 1) ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))))
           ℤ.·
           pos
           (suc
            (n ℕ.+ 29 ℕ.· suc n ℕ.+
             (n₁ ℕ.+ 0 ℕ.· suc n₁ ℕ.+
              (n ℕ.+ 59 ℕ.· suc n) ℕ.· suc (n₁ ℕ.+ 0 ℕ.· suc n₁))
             ℕ.· suc (n ℕ.+ 29 ℕ.· suc n))))
 _ = ℤ!

-- module TestWithℤ (v : ℕ → ℚ) where
--  -- open CommRingStr (ℚCommRing .snd)


--  _ : 5 · v 0 + 190 · v 1 +  6 · v 0 ≡ (v 1 · 100 + 11 · v 0 +  v 1 · 90) 
--  _ = ℚ!!

--  _ : [ 40 / 60 ] · v 0 + 190 · v 0 +  [ 50 / 30 ] · v 0 ≡ (v 0 · 100 + [ 70 / 30 ] · v 0 +  v 0 · 90) 
--  _ = ℚ!!

--  _ :  ([ 40 / 600000 ] · v 0 · 0 + 190 · v 1 · 0  +  [ 50 / 300000 ] · v 0 · 0)
--       ≡ (v 1 · 100 + [ 70 / 300000 ] · v 0 +  v 1 · 90) · 0 
--  _ = ℚ!!


-- -- -- module TestWithInv (f : ℕ → ℚ) where

-- -- --  -- test1 : ∀ {L} {_ : Unit} {_ : Unit} {δ₁} {ε₁} {r} {q : ℕ} →
-- -- --  --      fst (L ℚ₊· ((δ₁) ℚ₊+ (ε₁))) + f q + r ≡
-- -- --  --      fst ((L ℚ₊· δ₁) ℚ₊+ (L ℚ₊· ε₁))
-- -- --  -- test1 = ℚ!     

-- -- --  test1 : ∀ {L} {δ₁} {ε₁} →
-- -- --       fst (L ℚ₊· ((invℚ₊ L ℚ₊· δ₁) ℚ₊+ (invℚ₊ L ℚ₊· ε₁))) ≡
-- -- --       fst (δ₁ ℚ₊+ ε₁)
-- -- --  test1 = {!ℚ!!}     
-- -- -- -- -- {-
-- -- -- -- --   the following is not possible yet: the ring solver normalises the goal
-- -- -- -- --   and expands some of the definitions of the operations. A possible fix could be
-- -- -- -- --   to not normalize - but then one has to (at least) translate every use of a binary
-- -- -- -- --   minus. (#1101)

-- -- -- -- --   ex13 : (x y : ℤ) → (x · y) · 1r ≡ 1r · (y · x)
-- -- -- -- --   ex13 x y = solve! ℤCommRing
-- -- -- -- -- -}

-- -- -- -- -- --   ex0 : (a b : fst ℤCommRing) → a + b ≡ b + a
-- -- -- -- -- --   ex0 a b = solve! ℤCommRing

-- -- -- -- -- -- module Test (R : CommRing ℓ) (x y z : fst R) where
-- -- -- -- -- --   open CommRingStr (snd R)

-- -- -- -- -- --   _ : 0r ≡ 0r
-- -- -- -- -- --   _ = solve! R

-- -- -- -- -- --   _ :   1r · (1r + 0r)
-- -- -- -- -- --       ≡ (1r · 0r) + 1r
-- -- -- -- -- --   _ = solve! R

-- -- -- -- -- --   _ :   1r · 0r + (1r - 1r)
-- -- -- -- -- --       ≡ 0r - 0r
-- -- -- -- -- --   _ = solve! R

-- -- -- -- -- --   ex1 : x ≡ x
-- -- -- -- -- --   ex1 = solve! R

-- -- -- -- -- --   ex2 : (0r - 1r) · x ≡ 0r - x
-- -- -- -- -- --   ex2 = solve! R

-- -- -- -- -- --   ex3 : x + y ≡ y + x
-- -- -- -- -- --   ex3 = solve! R

-- -- -- -- -- --   ex4 : y ≡ (y - x) + x
-- -- -- -- -- --   ex4 = solve! R

-- -- -- -- -- --   ex5 : x ≡ (x - y) + y
-- -- -- -- -- --   ex5 = solve! R

-- -- -- -- -- --   ex6 : (x + y) · (x - y) ≡ x · x - y · y
-- -- -- -- -- --   ex6 = solve! R

-- -- -- -- -- --   {-
-- -- -- -- -- --     A bigger example:
-- -- -- -- -- --   -}
-- -- -- -- -- --   ex7 : (x + y) · (x + y) · (x + y) · (x + y)
-- -- -- -- -- --                 ≡ x · x · x · x + (scalar R 4) · x · x · x · y + (scalar R 6) · x · x · y · y
-- -- -- -- -- --                   + (scalar R 4) · x · y · y · y + y · y · y · y
-- -- -- -- -- --   ex7 = solve! R

-- -- -- -- -- --   {-
-- -- -- -- -- --     Examples that used to fail (see #513):
-- -- -- -- -- --   -}

-- -- -- -- -- --   ex8 : x · 0r ≡ 0r
-- -- -- -- -- --   ex8 = solve! R

-- -- -- -- -- --   ex9 : x · (y - z) ≡ x · y - x · z
-- -- -- -- -- --   ex9 = solve! R

-- -- -- -- -- --   {-
-- -- -- -- -- --     The solver should also deal with non-trivial terms in equations.
-- -- -- -- -- --     In the following example, such a term is given by "f x".
-- -- -- -- -- --   -}
-- -- -- -- -- --   pow : ℕ → fst R → fst R
-- -- -- -- -- --   pow (suc n) x = x · (pow n x)
-- -- -- -- -- --   pow (zero) x = 1r

-- -- -- -- -- --   module _ (f : fst R → fst R) (n : ℕ) where
-- -- -- -- -- --     ex10 : (x : (fst R)) → (pow n x) + 0r ≡ (pow n x)
-- -- -- -- -- --     ex10 x = solve! R

-- -- -- -- -- --     ex11 : (x : (fst R)) → (f x) + 0r ≡ (f x)
-- -- -- -- -- --     ex11 x = solve! R

-- -- -- -- -- -- module _ (R : CommRing ℓ) (A : CommAlgebra R ℓ') where
-- -- -- -- -- --   open CommRingStr ⦃...⦄
-- -- -- -- -- --   private
-- -- -- -- -- --     instance
-- -- -- -- -- --       _ : CommRingStr ⟨ A ⟩ₐ
-- -- -- -- -- --       _ = (A .fst .snd)
-- -- -- -- -- --   {-
-- -- -- -- -- --     The ring solver should also be able to deal with more complicated arguments
-- -- -- -- -- --     and operations with that are not given as the exact names in CommRingStr.
-- -- -- -- -- --   -}
-- -- -- -- -- --   ex12 : (x y : ⟨ A ⟩ₐ) → x + y ≡ y + x
-- -- -- -- -- --   ex12 x y = solve! (CommAlgebra→CommRing A)

-- -- -- -- -- -- module TestInPlaceSolving (R : CommRing ℓ) where
-- -- -- -- -- --    open CommRingStr (snd R)

-- -- -- -- -- --    testWithOneVariabl : (x : fst R) → x + 0r ≡ 0r + x
-- -- -- -- -- --    testWithOneVariabl x = solve! R

-- -- -- -- -- --    testWithTwoVariables :  (x y : fst R) → x + y ≡ y + x
-- -- -- -- -- --    testWithTwoVariables x y =
-- -- -- -- -- --      x + y                      ≡⟨ solve! R ⟩
-- -- -- -- -- --      y + x ∎

-- -- -- -- -- --    testEquationalReasoning : (x : fst R) → x + 0r ≡ 0r + x
-- -- -- -- -- --    testEquationalReasoning x =
-- -- -- -- -- --      x + 0r                       ≡⟨ solve! R ⟩
-- -- -- -- -- --      0r + x ∎

-- -- -- -- -- --    testEquationalReasoning' : (x : fst R) (p : 0r + x ≡ 1r) → x + 0r ≡ 1r
-- -- -- -- -- --    testEquationalReasoning' x p =
-- -- -- -- -- --      x + 0r              ≡⟨ solve! R ⟩
-- -- -- -- -- --      0r + x              ≡⟨ p ⟩
-- -- -- -- -- --      1r ∎
