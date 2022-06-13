{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.GradedRing.Instances.PolynomialsFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; +-assoc ; +-zero ; _∸_ ; snotz ) renaming (_+_ to _+n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
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
                   sameFiber
                   (λ _ → A)
                   (λ _ → snd (Ring→AbGroup ARing))
                   1r _·_ 0LeftAnnihilates 0RightAnnihilates
                   (λ a b c → ΣPathTransport→PathΣ _ _ ((+-assoc _ _ _) , (transportRefl _ ∙ ·Assoc _ _ _)))
                   (λ a → ΣPathTransport→PathΣ _ _ ((+-zero _) , (transportRefl _ ∙ ·IdR _)))
                   (λ a → ΣPathTransport→PathΣ _ _ (refl , (transportRefl _ ∙ ·IdL _)))
                   ·DistR+
                   ·DistL+
                 where
                 sameFiber : {i n : ℕ} → i ≤ n → i +n (n ∸ i) ≡ n
                 sameFiber {zero} {zero} p = refl
                 sameFiber {zero} {suc n} p = refl
                 sameFiber {suc i} {zero} p = ⊥.rec (¬-<-zero p)
                 sameFiber {suc i} {suc n} p = cong suc (sameFiber (pred-≤-pred p))
