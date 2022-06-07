{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.GradedRing.Instances.Polynomials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.NatVec
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.Base
open import Cubical.Algebra.GradedRing.DirectSumHIT

private variable
  ℓ : Level

open Iso

module _
  (ARing@(A , Astr) : Ring ℓ)
  (n : ℕ)
  where

  open RingStr Astr
  open RingTheory ARing

  PolyGradedRing : GradedRing ℓ-zero ℓ
  PolyGradedRing = makeGradedRingSelf
                   (NatVecMonoid n)
                   (λ _ → A)
                   (λ _ → snd (Ring→AbGroup ARing))
                   1r _·_ 0LeftAnnihilates 0RightAnnihilates
                   (λ a b c → ΣPathTransport→PathΣ _ _ ((+n-vec-assoc _ _ _) , (transportRefl _ ∙ ·Assoc _ _ _)))
                   (λ a → ΣPathTransport→PathΣ _ _ ((+n-vec-rid _) , (transportRefl _ ∙ ·Rid _)))
                   (λ a → ΣPathTransport→PathΣ _ _ ((+n-vec-lid _) , (transportRefl _ ∙ ·Lid _)))
                   ·Rdist+
                   ·Ldist+
