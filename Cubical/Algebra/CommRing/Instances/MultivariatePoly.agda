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
  _+_ (snd PolyCommRing) = _Poly+_
  _·_ (snd PolyCommRing) = _Poly*_
  - snd PolyCommRing = Poly-inv
  isCommRing (snd PolyCommRing) = makeIsCommRing
                                  trunc
                                  Poly+-assoc
                                  Poly+-Rid
                                  Poly+-rinv
                                  Poly+-comm
                                  Poly*-assoc
                                  Poly*-Rid
                                  Poly*-Rdist
                                  Poly*-comm



-----------------------------------------------------------------------------
-- Notation and syntax in the case 1,2,3 and ℤ

ℤ[X] : CommRing ℓ-zero
ℤ[X] = PolyCommRing ℤ 1

ℤ[x] : Type ℓ-zero
ℤ[x] = fst ℤ[X]

ℤ[X,Y] : CommRing ℓ-zero
ℤ[X,Y] = PolyCommRing ℤ 2

ℤ[x,y] : Type ℓ-zero
ℤ[x,y] = fst ℤ[X,Y]

ℤ[X,Y,Z] : CommRing ℓ-zero
ℤ[X,Y,Z] = PolyCommRing ℤ 3

ℤ[x,y,z] : Type ℓ-zero
ℤ[x,y,z] = fst ℤ[X,Y,Z]

module _
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  A[X1,···,Xn] : CommRing ℓ
  A[X1,···,Xn] = PolyCommRing Ar n

  A[x1,···,xn] : Type ℓ
  A[x1,···,xn] = fst (A[X1,···,Xn])

ℤ[X1,···,Xn] : (n : ℕ) → CommRing ℓ-zero
ℤ[X1,···,Xn] n = A[X1,···,Xn] ℤ n

ℤ[x1,···,xn] : (n : ℕ) → Type ℓ-zero
ℤ[x1,···,xn] n = fst (ℤ[X1,···,Xn] n)
