{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- General Nth polynome

module _
  (A : CommRing ℓ)
  (n : ℕ)
  where

  open CommRingStr
  open RingTheory (CommRing→Ring A)
  open Nth-Poly-structure A n

  PolyCommRing : CommRing ℓ
  fst PolyCommRing = Poly A n
  0r (snd PolyCommRing) = 0P
  1r (snd PolyCommRing) = 1P
  _+_ (snd PolyCommRing) = _poly+_
  _·_ (snd PolyCommRing) = _poly*_
  - snd PolyCommRing = polyInv
  isCommRing (snd PolyCommRing) = makeIsCommRing
                                  trunc
                                  poly+Assoc
                                  poly+IdR
                                  poly+InvR
                                  poly+Comm
                                  poly*Assoc
                                  poly*IdR
                                  poly*DistR
                                  poly*Comm


-----------------------------------------------------------------------------
-- Notation and syntax in the case 1,2,3 and ℤ

module _
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  A[X1,···,Xn] : CommRing ℓ
  A[X1,···,Xn] = PolyCommRing Ar n

  A[x1,···,xn] : Type ℓ
  A[x1,···,xn] = fst (A[X1,···,Xn])
