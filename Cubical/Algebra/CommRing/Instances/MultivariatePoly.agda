{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.MultivariatePoly where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat

open import Cubical.Algebra.Monoid.Instances.NatVec
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.GradedRing.DirectSumHIT
open import Cubical.Algebra.GradedRing.Instances.Polynomials
open import Cubical.Algebra.CommRing.Instances.Int


-- open import Cubical.Algebra.Polynomials.Multivariate.Base
-- open import Cubical.Algebra.Polynomials.Multivariate.Properties

private variable
  ℓ : Level

-----------------------------------------------------------------------------
-- General Nth polynome

module _
  (ACommRing@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  open CommRingStr Astr
  open RingTheory (CommRing→Ring ACommRing)

  PolyCommRing : CommRing ℓ
  PolyCommRing = ⊕HITgradedRing-CommRing
                 (NatVecMonoid n)
                 (λ _ → A)
                 (λ _ → snd (Ring→AbGroup (CommRing→Ring ACommRing)))
                 1r _·_ 0LeftAnnihilates 0RightAnnihilates
                 (λ a b c → ΣPathTransport→PathΣ _ _ ((+n-vec-assoc _ _ _) , (transportRefl _ ∙ ·Assoc _ _ _)))
                 (λ a → ΣPathTransport→PathΣ _ _ ((+n-vec-rid _) , (transportRefl _ ∙ ·Rid _)))
                 (λ a → ΣPathTransport→PathΣ _ _ ((+n-vec-lid _) , (transportRefl _ ∙ ·Lid _)))
                 ·Rdist+
                 ·Ldist+
                 λ x y → ΣPathTransport→PathΣ _ _ ((+n-vec-comm _ _) , (transportRefl _ ∙ ·Comm _ _))


-----------------------------------------------------------------------------
-- Notation and syntax in the case 1,2,3 and ℤ

module _
  (Ar@(A , Astr) : CommRing ℓ)
  (n : ℕ)
  where

  Poly : Type ℓ
  Poly = fst (PolyCommRing Ar n)

-- Possible renaming
-- (PolyCommRing to A[X1,···,Xn] ; Poly to A[x1,···,xn])
