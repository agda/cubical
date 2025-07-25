{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.GradedRing.Instances.PolynomialsFun where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_) renaming (_+_ to _+n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.Base
open import Cubical.Algebra.GradedRing.DirectSumFun

private variable
  ℓ : Level

module _
  (ARing@(A , Astr) : Ring ℓ)
  (n : ℕ)
  where

  open RingStr Astr
  open RingTheory ARing

  PolyGradedRing : GradedRing ℓ-zero ℓ
  PolyGradedRing = ⊕Fun-GradedRing
                   _+n_ (makeIsMonoid isSetℕ +-assoc +-zero λ _ → refl) (λ _ _ → refl)
                   (λ _ → A)
                   (λ _ → snd (Ring→AbGroup ARing))
                   1r _·_ 0LeftAnnihilates 0RightAnnihilates
                   (λ a b c → ΣPathP ((+-assoc _ _ _) , (·Assoc _ _ _)))
                   (λ a → ΣPathP ((+-zero _) , (·IdR _)))
                   (λ a → ΣPathP (refl , (·IdL _)))
                   ·DistR+
                   ·DistL+
