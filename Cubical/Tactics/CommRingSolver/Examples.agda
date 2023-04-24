{-# OPTIONS --safe #-}
module Cubical.Tactics.CommRingSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Int.Base hiding (ℤ; _+_ ; _·_ ; _-_)
open import Cubical.Data.List

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommAlgebra
open import Cubical.Tactics.CommRingSolver.Reflection

private
  variable
    ℓ ℓ' : Level

module TestErrors (R : CommRing ℓ) where
  open CommRingStr (snd R)

  {-
    The following should give an type checking error,
    making the user aware that the problem is, that 'Type₀'
    is not a CommRing.
  -}
  {-
  _ : 0r ≡ 0r
  _ = solve Type₀
  -}

module TestWithℤ where
  open CommRingStr (ℤCommRing .snd)

  _ : (a b : fst ℤCommRing) → a + b ≡ b + a
  _ = solve ℤCommRing

module Test (R : CommRing ℓ) where
  open CommRingStr (snd R)

  _ : 0r ≡ 0r
  _ = solve R

  _ :   1r · (1r + 0r)
      ≡ (1r · 0r) + 1r
  _ = solve R

  _ :   1r · 0r + (1r - 1r)
      ≡ 0r - 0r
  _ = solve R

  _ : ∀ x → x ≡ x
  _ = solve R

  _ : ∀ x y → x ≡ x
  _ = solve R

  _ : ∀ x y → x + y ≡ y + x
  _ = solve R

  _ : ∀ x y → y ≡ (y - x) + x
  _ = solve R

  _ : ∀ x y → x ≡ (x - y) + y
  _ = solve R

  _ : ∀ x y → (x + y) · (x - y) ≡ x · x - y · y
  _ = solve R

  {-
    A bigger example, copied from the other example files:
  -}
  _ : (x y z : (fst R)) → (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + (fromℤ R 4) · x · x · x · y + (fromℤ R 6) · x · x · y · y
                  + (fromℤ R 4) · x · y · y · y + y · y · y · y
  _ = solve R

  {-
    Examples that used to fail (see #513):
  -}

  _ : (x : (fst R)) → x · 0r ≡ 0r
  _ = solve R

  _ : (x y z : (fst R)) → x · (y - z) ≡ x · y - x · z
  _ = solve R

module _ (R : CommRing ℓ) (A : CommAlgebra R ℓ') where
  open CommAlgebraStr {{...}}
  private
    instance
      _ = (snd A)
  {-
    The ring solver should also be able to deal with more complicated arguments
    and operations with that are not given as the exact names in CommRingStr.
  -}
  _ : (x y : ⟨ A ⟩) → x + y ≡ y + x
  _ = solve (CommAlgebra→CommRing A)


module TestInPlaceSolving (R : CommRing ℓ) where
   open CommRingStr (snd R)

   testWithOneVariabl : (x : fst R) → x + 0r ≡ 0r + x
   testWithOneVariabl x = solveInPlace R (x ∷ [])

   testWithTwoVariables :  (x y : fst R) → x + y ≡ y + x
   testWithTwoVariables x y =
     x + y                      ≡⟨ solveInPlace R (x ∷ y ∷ []) ⟩
     y + x ∎

   testEquationalReasoning : (x : fst R) → x + 0r ≡ 0r + x
   testEquationalReasoning x =
     x + 0r                       ≡⟨ solveInPlace R (x ∷ []) ⟩
     0r + x ∎

   {-
     So far, solving during equational reasoning has a serious
     restriction:
     The solver identifies variables by deBruijn indices and the variables
     appearing in the equations to solve need to have indices 0,...,n. This
     entails that in the following code, the order of 'p' and 'x' cannot be
     switched.
   -}
   testEquationalReasoning' : (p : (y : fst R) → 0r + y ≡ 1r) (x : fst R) → x + 0r ≡ 1r
   testEquationalReasoning' p x =
     x + 0r              ≡⟨ solveInPlace R (x ∷ []) ⟩
     0r + x              ≡⟨ p x ⟩
     1r ∎
