{-# OPTIONS --quote-metas #-}
module Cubical.Tactics.CommRingSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; _-_ ; -_)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Nat using (ℕ; suc; zero)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommAlgebra

open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver renaming (solve! to generic-solve!)
import Cubical.Tactics.CommRingSolver.RawAlgebra as RA

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

-- module TestWithℤ where
--   open CommRingStr (ℤCommRing .snd)

-- {-
--   the following is not possible yet: the ring solver normalises the goal
--   and expands some of the definitions of the operations. A possible fix could be
--   to not normalize - but then one has to (at least) translate every use of a binary
--   minus. (#1101)

--   ex13 : (x y : ℤ) → (x · y) · 1r ≡ 1r · (y · x)
--   ex13 x y = solve! ℤCommRing


-- -}
--   open CommRingSolverMacros

--   ex0 : (a b : fst ℤCommRing) → a + b ≡ b + a
--   ex0 a b = solve! ℤCommRing



-- module Test0 (R : CommRing ℓ) where
--   open CommRingStr (snd R)
--   open RingTheory (CommRing→Ring R) using () renaming (fromℤ to scalar)

--   open SolveOverℤ.Generic R

--   relTrans : BinaryRelation.isTrans {A = ((fst R) × (Σ[ b ∈ (fst R) ] (b ≡ 0r → ⊥)))}
--                λ  (a , (b , _)) (c , (d , _)) → a · d ≡ c · b
--   relTrans (a , (b , _)) (a' , (b' , b'≢0)) (a'' , (b'' , _)) p q =
--     {!!}
--    where
--     u : b' · (- (a · b'') + b · a'') ≡ 0r
--     u = eliminate! a' p q []


module Test0intDom (R : CommRing ℓ) (isIntDom : _) where
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R) renaming (fromℤ to scalar)

  open SolveOverℤ.Reasonable R isIntDom

  relTrans : BinaryRelation.isTrans {A = ((fst R) × (Σ[ b ∈ (fst R) ] (b ≡ 0r → ⊥)))}
               λ  (a , (b , _)) (c , (d , _)) → a · d ≡ c · b
  relTrans (a , (b , _)) (a' , (b' , b'≢0)) (a'' , (b'' , _)) p q =
    sym (equalByDifference _ _ (solve! ∙ eliminate! a' p q P[ b'≢0 ]))

module Test (R : CommRing ℓ) (x y z w v : fst R) where
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R) using () renaming (fromℤ to scalar ; fromℕ to ⟨_⟩ₙ)
  open Exponentiation R using (_^_)

  open SolveOverℤ.Generic

  _ : 0r ≡ 0r
  _ = solve! R

  _ : 1r ≡ 1r
  _ = solve! R


  _ :   1r · (1r + 0r)
      ≡ (1r · 0r) + 1r
  _ = solve! R

  _ :   1r · 0r + (1r - 1r)
      ≡ 0r - 0r
  _ = solve! R

  ex1 : x ≡ x
  ex1 = solve! R

  ex2 : (0r - 1r) · x ≡ 0r - x
  ex2 = solve! R

  ex3 : x + y ≡ y + x
  ex3 = solve! R

  ex4 : y ≡ (y - x) + x
  ex4 = solve! R

  -- xHole : fst R
  -- xHole = {!!}

  ex5 : x ≡ (x - y) + y
  ex5 = solve! R

  ex6 : (x + y) · (x - y) ≡ x · x - y · y
  ex6 = solve! R

  -- module RelTest where
  --  relTest :  (fst R) × (fst R) → (fst R) × (fst R) → Type ℓ
  --  relTest (a , b) (c , d) = a · d ≡ c · b

  --  relTrans : BinaryRelation.isTrans relTest
  --  relTrans (a , b) (a' , b') (a'' , b'') p q =
  --    {!!}
  --   where
  --    u : b' · (- (a · b'') + b · a'') ≡ 0r
  --    u = eliminate! R a' p q []


  ex7 : (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + (scalar 4) · x · x · x · y + (scalar 6) · x · x · y · y
                  + (scalar 4) · x · y · y · y + y · y · y · y
  ex7 = solve! R

  module _ (p : _)
           (p1 : _) where
   ex7' : v + z · x + y + w · x + (- w) + v ≡ (scalar 2 · v) + x + y + x + scalar 2
   ex7' =
    ring! R (v ∷ y ∷ x ∷ [])
       (p ∷ P[ p1 ])

  exNorm0 : (x + y + y + x - y  + scalar 5  -  x + (- scalar 1)) · x · (scalar 3) ≡
            (⟨ 3 ⟩ₙ · x · (⟨ 4 ⟩ₙ + y + x))
  exNorm0 = normalize! R


  exNorm : (x + y) · ((x + x) - y - y) + scalar 5 + (- scalar 1) ≡
            (⟨ 2 ⟩ₙ · (⟨ 2 ⟩ₙ + x ^ 2 - y ^ 2))
  exNorm = normalize! R


  exNorm2 : v + z · x + y + w · x + (- w) + v + (scalar 2 · v) + x + y + x + scalar 2 ≡
             (⟨ 2 ⟩ₙ - w + ⟨ 4 ⟩ₙ · v + ⟨ 2 ⟩ₙ · y + ⟨ 2 ⟩ₙ · x + z · x + w · x)
  exNorm2 = normalize! R


  exNorm3 : - (y + z) + ( - y - z)  - x - x · ⟨ 3 ⟩ₙ ≡
               (- ⟨ 2 ⟩ₙ · (y + z + ⟨ 2 ⟩ₙ · x))
  exNorm3 = normalize! R


  -- exNorm : (x + y) · (x - y) + scalar 2 + (- scalar 1) ≡ (1r + x ^ 2 - y ^ 2)
  -- exNorm = normalize! R

  -- exNorm2 : v + z · x + y + w · x + (- w) + v + (scalar 2 · v) + x + y + x + scalar 2 ≡
  --            (⟨ 2 ⟩ₙ - w + ⟨ 4 ⟩ₙ · v + ⟨ 2 ⟩ₙ · y + ⟨ 2 ⟩ₙ · x + z · x + w · x)
  -- exNorm2 = normalize! R

  -- exNorm3 : - y - z - x - x ≡ ?
  -- exNorm3 = normalize! R


--   module SolveForExamples
--     (eq1 : ( y · y + v + z · x + w · x + (- w) + v + (scalar 2 · v) ≡ - (y · y) - x  - x - scalar 2))
--     (eq2 :  y + (x · x · x)  ≡ scalar 2)
--     (eq3 : ( y · scalar 2 · y · v + v + z · x + w · x + (- w) + v + (scalar 2 · v) ≡ - (y · w · y · scalar 4) · v - x  - x - scalar 2))
--          where

--     solveForEx : ⟨ 2 ⟩ₙ · y ^ 2 ≡
--                   - ⟨ 2 ⟩ₙ + w - ⟨ 4 ⟩ₙ · v - ⟨ 2 ⟩ₙ · x - z · x - w · x
--     solveForEx = solveFor! R y eq1

--     solveForEx2 : y ≡ ⟨ 2 ⟩ₙ - x ^ 3
--     solveForEx2 = solveFor! R y eq2

--     solveForEx3 : ⟨ 2 ⟩ₙ · v · (⟨ 1 ⟩ₙ + ⟨ 2 ⟩ₙ · w) · y ^ 2 ≡
--                    - ⟨ 2 ⟩ₙ + w - ⟨ 4 ⟩ₙ · v - ⟨ 2 ⟩ₙ · x - z · x - w · x
--     solveForEx3 = solveFor! R y eq3


-- -- -- --   {-
-- -- -- --     Examples that used to fail (see #513):
-- -- -- --   -}

-- -- -- --   ex8 : x · 0r ≡ 0r
-- -- -- --   ex8 = solve! R

-- -- -- --   ex9 : x · (y - z) ≡ x · y - x · z
-- -- -- --   ex9 = solve! R

-- -- -- --   {-
-- -- -- --     The solver should also deal with non-trivial terms in equations.
-- -- -- --     In the following example, such a term is given by "f x".
-- -- -- --   -}
-- -- -- --   pow : ℕ → fst R → fst R
-- -- -- --   pow (suc n) x = x · (pow n x)
-- -- -- --   pow (zero) x = 1r

-- -- -- --   module _ (f : fst R → fst R) (n : ℕ) where
-- -- -- --     ex10 : (x : (fst R)) → (pow n x) + 0r ≡ (pow n x)
-- -- -- --     ex10 x = solve! R

-- -- -- --     ex11 : (x : (fst R)) → (f x) + 0r ≡ (f x)
-- -- -- --     ex11 x = solve! R

-- -- -- -- module _ (R : CommRing ℓ) (A : CommAlgebra R ℓ') where
-- -- -- --   open CommRingStr ⦃...⦄
-- -- -- --   private
-- -- -- --     instance
-- -- -- --       _ : CommRingStr ⟨ A ⟩ₐ
-- -- -- --       _ = (A .fst .snd)
-- -- -- --   {-
-- -- -- --     The ring solver should also be able to deal with more complicated arguments
-- -- -- --     and operations with that are not given as the exact names in CommRingStr.
-- -- -- --   -}
-- -- -- --   ex12 : (x y : ⟨ A ⟩ₐ) → x + y ≡ y + x
-- -- -- --   ex12 x y = solve! (CommAlgebra→CommRing A)

-- -- -- -- module TestInPlaceSolving (R : CommRing ℓ) where
-- -- -- --    open CommRingStr (snd R)

-- -- -- --    testWithOneVariabl : (x : fst R) → x + 0r ≡ 0r + x
-- -- -- --    testWithOneVariabl x = solve! R

-- -- -- --    testWithTwoVariables :  (x y : fst R) → x + y ≡ y + x
-- -- -- --    testWithTwoVariables x y =
-- -- -- --      x + y                      ≡⟨ solve! R ⟩
-- -- -- --      y + x ∎

-- -- -- --    testEquationalReasoning : (x : fst R) → x + 0r ≡ 0r + x
-- -- -- --    testEquationalReasoning x =
-- -- -- --      x + 0r                       ≡⟨ solve! R ⟩
-- -- -- --      0r + x ∎

-- -- -- --    testEquationalReasoning' : (x : fst R) (p : 0r + x ≡ 1r) → x + 0r ≡ 1r
-- -- -- --    testEquationalReasoning' x p =
-- -- -- --      x + 0r              ≡⟨ solve! R ⟩
-- -- -- --      0r + x              ≡⟨ p ⟩
-- -- -- --      1r ∎
