{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly-notationZ where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient



-- Notations for ℤ polynomial rings

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

ℤ[X1,···,Xn] : (n : ℕ) → CommRing ℓ-zero
ℤ[X1,···,Xn] n = A[X1,···,Xn] ℤ n

ℤ[x1,···,xn] : (n : ℕ) → Type ℓ-zero
ℤ[x1,···,xn] n = fst (ℤ[X1,···,Xn] n)



-- Notation for quotiented ℤ polynomial ring

<X> : FinVec ℤ[x] 1
<X> = <Xkʲ> ℤ 1 0 1

<X²> : FinVec ℤ[x] 1
<X²> = <Xkʲ> ℤ 1 0 2

<X³> : FinVec ℤ[x] 1
<X³> = <Xkʲ> ℤ 1 0 3

<Xᵏ> : (k  : ℕ) → FinVec ℤ[x] 1
<Xᵏ> k = <Xkʲ> ℤ 1 0 k

ℤ[X]/X : CommRing ℓ-zero
ℤ[X]/X = A[X1,···,Xn]/<Xkʲ> ℤ 1 0 1

ℤ[x]/x : Type ℓ-zero
ℤ[x]/x = fst ℤ[X]/X

ℤ[X]/X² : CommRing ℓ-zero
ℤ[X]/X² = A[X1,···,Xn]/<Xkʲ> ℤ 1 0 2

ℤ[x]/x² : Type ℓ-zero
ℤ[x]/x² = fst ℤ[X]/X²

ℤ[X]/X³ : CommRing ℓ-zero
ℤ[X]/X³ = A[X1,···,Xn]/<Xkʲ> ℤ 1 0 3

ℤ[x]/x³ : Type ℓ-zero
ℤ[x]/x³ = fst ℤ[X]/X³

ℤ[X1,···,Xn]/<X1,···,Xn> : (n : ℕ) → CommRing ℓ-zero
ℤ[X1,···,Xn]/<X1,···,Xn> n = A[X1,···,Xn]/<X1,···,Xn> ℤ n

ℤ[x1,···,xn]/<x1,···,xn> : (n : ℕ) → Type ℓ-zero
ℤ[x1,···,xn]/<x1,···,xn> n = fst (ℤ[X1,···,Xn]/<X1,···,Xn> n)


-- Warning there is two possible definitions of ℤ[X]
-- they only holds up to a path

ℤ'[X]/X : CommRing ℓ-zero
ℤ'[X]/X = A[X1,···,Xn]/<X1,···,Xn> ℤ 1

equivℤ[X] : ℤ'[X]/X ≡ ℤ[X]/X
equivℤ[X] = cong (λ X → (A[X1,···,Xn] ℤ 1) / (genIdeal ((A[X1,···,Xn] ℤ 1)) X))
                   (funExt (λ {zero → refl }))
