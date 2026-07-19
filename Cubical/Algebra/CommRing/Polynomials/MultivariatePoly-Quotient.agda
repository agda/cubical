module Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-Quotient where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)

open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly
  renaming (PolyCommRing to A[X1,···,Xn] ; Poly to A[x1,···,xn])

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- General Nth polynome / quotient
-- Better to declare an alias

PolyCommRing-Quotient : (A : CommRing ℓ) → {n m : ℕ} → FinVec (fst (A[X1,···,Xn] A n)) m → CommRing ℓ
PolyCommRing-Quotient A {n} {m} v = A[X1,···,Xn] A n / genIdeal (A[X1,···,Xn] A n) v

-----------------------------------------------------------------------------
-- Notation in the general case and some real cases 1, 2, 3

module _
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  <Xkʲ> : (k j : ℕ) →  FinVec (A[x1,···,xn] Ar n) 1
  <Xkʲ> k j zero = base (genδℕ-Vec n k j 0) (CommRingStr.1r Astr)

  A[X1,···,Xn]/<Xkʲ> : (k j : ℕ) → CommRing ℓ
  A[X1,···,Xn]/<Xkʲ> k j = (A[X1,···,Xn] Ar n) / (genIdeal ((A[X1,···,Xn] Ar n)) (<Xkʲ> k j))

  A[x1,···,xn]/<xkʲ> : (k j : ℕ) → Type ℓ
  A[x1,···,xn]/<xkʲ> k j = fst (A[X1,···,Xn]/<Xkʲ> k j)

  <X1,···,Xn> : FinVec (A[x1,···,xn] Ar n) n
  <X1,···,Xn> = λ k → base (δℕ-Vec n (toℕ k)) (CommRingStr.1r Astr)

  A[X1,···,Xn]/<X1,···,Xn> : CommRing ℓ
  A[X1,···,Xn]/<X1,···,Xn> = (A[X1,···,Xn] Ar n) / (genIdeal ((A[X1,···,Xn] Ar n)) <X1,···,Xn>)

  A[x1,···,xn]/<x1,···,xn> : Type ℓ
  A[x1,···,xn]/<x1,···,xn> = fst A[X1,···,Xn]/<X1,···,Xn>
