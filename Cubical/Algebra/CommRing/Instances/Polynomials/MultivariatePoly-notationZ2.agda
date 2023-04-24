{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-notationZ2 where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.IntMod

open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
     renaming (PolyCommRing to A[X1,···,Xn] ; Poly to A[x1,···,xn])
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient



-- Notations for ℤ/2 polynomial rings

ℤ/2[X] : CommRing ℓ-zero
ℤ/2[X] = A[X1,···,Xn] ℤ/2CommRing 1

ℤ/2[x] : Type ℓ-zero
ℤ/2[x] = fst ℤ/2[X]

ℤ/2[X,Y] : CommRing ℓ-zero
ℤ/2[X,Y] = A[X1,···,Xn] ℤ/2CommRing 2

ℤ/2[x,y] : Type ℓ-zero
ℤ/2[x,y] = fst ℤ/2[X,Y]

ℤ/2[X,Y,Z] : CommRing ℓ-zero
ℤ/2[X,Y,Z] = A[X1,···,Xn] ℤ/2CommRing 3

ℤ/2[x,y,z] : Type ℓ-zero
ℤ/2[x,y,z] = fst ℤ/2[X,Y,Z]

ℤ/2[X1,···,Xn] : (n : ℕ) → CommRing ℓ-zero
ℤ/2[X1,···,Xn] n = A[X1,···,Xn] ℤ/2CommRing n

ℤ/2[x1,···,xn] : (n : ℕ) → Type ℓ-zero
ℤ/2[x1,···,xn] n = fst (ℤ/2[X1,···,Xn] n)



-- Notation for quotiented ℤ/2 polynomial ring

<X> : FinVec ℤ/2[x] 1
<X> = <Xkʲ> ℤ/2CommRing 1 0 1

<X²> : FinVec ℤ/2[x] 1
<X²> = <Xkʲ> ℤ/2CommRing 1 0 2

<X³> : FinVec ℤ/2[x] 1
<X³> = <Xkʲ> ℤ/2CommRing 1 0 3

<Xᵏ> : (k  : ℕ) → FinVec ℤ/2[x] 1
<Xᵏ> k = <Xkʲ> ℤ/2CommRing 1 0 k
