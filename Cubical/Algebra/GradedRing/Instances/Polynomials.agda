{-# OPTIONS --lossy-unification #-}
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
open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆

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
                   (λ a b c → ΣPathP ((+n-vec-assoc _ _ _) , (·Assoc _ _ _)))
                   (λ a → ΣPathP ((+n-vec-rid _) , (·IdR _)))
                   (λ a → ΣPathP ((+n-vec-lid _) , (·IdL _)))
                   ·DistR+
                   ·DistL+
