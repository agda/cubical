{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient-notationZ where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.QuotientRing
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤ to ℤCR)

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly-Quotient

private variable
  ℓ : Level

-- good notation in case A = ℤ


-- in the general case

<X> : FinVec ℤ[x] 1
<X> = <Xkʲ> ℤCR 1 0 1

<X²> : FinVec ℤ[x] 1
<X²> = <Xkʲ> ℤCR 1 0 2

<X³> : FinVec ℤ[x] 1
<X³> = <Xkʲ> ℤCR 1 0 3

<Xᵏ> : (k  : ℕ) → FinVec ℤ[x] 1
<Xᵏ> k = <Xkʲ> ℤCR 1 0 k

ℤ[X]/X : CommRing ℓ-zero
ℤ[X]/X = A[X1,···,Xn]/<Xkʲ> ℤCR 1 0 1

ℤ[x]/x : Type ℓ-zero
ℤ[x]/x = fst ℤ[X]/X

ℤ[X]/X² : CommRing ℓ-zero
ℤ[X]/X² = A[X1,···,Xn]/<Xkʲ> ℤCR 1 0 2

ℤ[x]/x² : Type ℓ-zero
ℤ[x]/x² = fst ℤ[X]/X²

ℤ[X]/X³ : CommRing ℓ-zero
ℤ[X]/X³ = A[X1,···,Xn]/<Xkʲ> ℤCR 1 0 3

ℤ[x]/x³ : Type ℓ-zero
ℤ[x]/x³ = fst ℤ[X]/X³

ℤ[X1,···,Xn]/<X1,···,Xn> : (n : ℕ) → CommRing ℓ-zero
ℤ[X1,···,Xn]/<X1,···,Xn> n = A[X1,···,Xn]/<X1,···,Xn> ℤCR n

ℤ[x1,···,xn]/<x1,···,xn> : (n : ℕ) → Type ℓ-zero
ℤ[x1,···,xn]/<x1,···,xn> n = fst (ℤ[X1,···,Xn]/<X1,···,Xn> n)

-- Warning there is now two possible definition of ℤ[X]

ℤ'[X]/X : CommRing ℓ-zero
ℤ'[X]/X = A[X1,···,Xn]/<X1,···,Xn> ℤCR 1

experiment1 : ℤ'[X]/X ≡ ℤ[X]/X
experiment1 = cong₂ _/_ refl (cong₂ genIdeal refl helper)
  where
  helper : <X1,···,Xn> ℤCR 1 ≡ <X>
  helper = funExt (λ {zero → refl })

equivℤ[X] : ℤ'[X]/X ≡ ℤ[X]/X
equivℤ[X] = cong (λ X → (A[X1,···,Xn] ℤCR 1) / (genIdeal ((A[X1,···,Xn] ℤCR 1)) X))
                   (funExt (λ {zero → refl }))
