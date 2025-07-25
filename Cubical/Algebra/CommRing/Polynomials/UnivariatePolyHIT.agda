{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.CommRing.Polynomials.UnivariatePolyHIT where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_) renaming (_+_ to _+n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.GradedRing.DirectSumHIT

private variable
  ℓ : Level

open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆
open ExtensionCommRing

module _
  (ACommRing@(A , Astr) : CommRing ℓ)
  where

  open CommRingStr Astr
  open RingTheory (CommRing→Ring ACommRing)

  UnivariatePolyHIT-CommRing : CommRing ℓ
  UnivariatePolyHIT-CommRing = ⊕HITgradedRing-CommRing
                   NatMonoid
                   (λ _ → A)
                   (λ _ → snd (Ring→AbGroup (CommRing→Ring ACommRing)))
                   1r _·_ 0LeftAnnihilates 0RightAnnihilates
                   (λ a b c → ΣPathP ((+-assoc _ _ _) , (·Assoc _ _ _)))
                   (λ a → ΣPathP ((+-zero _) , (·IdR _)))
                   (λ a → ΣPathP (refl , (·IdL _)))
                   ·DistR+
                   ·DistL+
                   λ x y → ΣPathP ((+-comm _ _) , (·Comm _ _))

nUnivariatePolyHIT : (A' : CommRing ℓ) → (n : ℕ) → CommRing ℓ
nUnivariatePolyHIT A' zero = A'
nUnivariatePolyHIT A' (suc n) = UnivariatePolyHIT-CommRing (nUnivariatePolyHIT A' n)
