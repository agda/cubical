{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Instances.UnivariatePolyFun where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_·_) renaming (_+_ to _+n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.GradedRing.DirectSumFun

private variable
  ℓ : Level

module _
  (ACommRing@(A , Astr) : CommRing ℓ)
  where

  open CommRingStr Astr
  open RingTheory (CommRing→Ring ACommRing)

  UnivariatePolyFun-CommRing : CommRing ℓ
  UnivariatePolyFun-CommRing = ⊕FunGradedRing-CommRing
                   _+n_ (makeIsMonoid isSetℕ +-assoc +-zero λ _ → refl) (λ _ _ → refl)
                   sameFiber
                   (λ _ → A)
                   (λ _ → snd (Ring→AbGroup (CommRing→Ring ACommRing)))
                   1r _·_ 0LeftAnnihilates 0RightAnnihilates
                   (λ a b c → ΣPathP ((+-assoc _ _ _) , (·Assoc _ _ _)))
                   (λ a → ΣPathP ((+-zero _) , (·IdR _)))
                   (λ a → ΣPathP (refl , (·IdL _)))
                   ·DistR+
                   ·DistL+
                   λ x y → ΣPathP ((+-comm _ _) , (·Comm _ _))
                 where
                 sameFiber : {i n : ℕ} → i ≤ n → i +n (n ∸ i) ≡ n
                 sameFiber {zero} {zero} p = refl
                 sameFiber {zero} {suc n} p = refl
                 sameFiber {suc i} {zero} p = ⊥.rec (¬-<-zero p)
                 sameFiber {suc i} {suc n} p = cong suc (sameFiber (pred-≤-pred p))

nUnivariatePolyFun : (A' : CommRing ℓ) → (n : ℕ) → CommRing ℓ
nUnivariatePolyFun A' zero = A'
nUnivariatePolyFun A' (suc n) = UnivariatePolyFun-CommRing (nUnivariatePolyFun A' n)
