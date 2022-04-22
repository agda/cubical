{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat renaming(_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
-- open import Cubical.ZCohomology.CohomologyRings.Unit

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- General Nth polynome / quotient
-- Better to declare an alias

PolyCommRing-Quotient : (A : CommRing ℓ) → {n m : ℕ} → FinVec (fst (PolyCommRing A n)) m → CommRing ℓ
PolyCommRing-Quotient A {n} {m} v = PolyCommRing A n / genIdeal (PolyCommRing A n) v

-----------------------------------------------------------------------------
-- Notation and syntax in the case 1

<X> : FinVec ℤ[x] 1
<X> zero = base (1 ∷ []) (CommRingStr.1r (snd ℤ))

ℤ[X]/X : CommRing ℓ-zero
ℤ[X]/X = ℤ[X] / genIdeal ℤ[X] <X>

ℤ[x]/x : Type ℓ-zero
ℤ[x]/x = fst ℤ[X]/X

<X²> : FinVec ℤ[x] 1
<X²> zero = base (2 ∷ []) (CommRingStr.1r (snd ℤ))

ℤ[X]/X² : CommRing ℓ-zero
ℤ[X]/X² = ℤ[X] / genIdeal ℤ[X] <X²>

ℤ[x]/x² : Type ℓ-zero
ℤ[x]/x² = fst ℤ[X]/X²

<X³> : FinVec ℤ[x] 1
<X³> zero = base (2 ∷ []) (CommRingStr.1r (snd ℤ))

ℤ[X]/X³ : CommRing ℓ-zero
ℤ[X]/X³ = ℤ[X] / genIdeal ℤ[X] <X³>

ℤ[x]/x³ : Type ℓ-zero
ℤ[x]/x³ = fst ℤ[X]/X³

<Xᵏ> : (k  : ℕ) → FinVec ℤ[x] 1
<Xᵏ> k zero = base (k ∷ []) (CommRingStr.1r (snd ℤ))

ℤ[X]/Xᵏ : (k : ℕ) → CommRing ℓ-zero
ℤ[X]/Xᵏ k = ℤ[X] / genIdeal ℤ[X] (<Xᵏ> k)
