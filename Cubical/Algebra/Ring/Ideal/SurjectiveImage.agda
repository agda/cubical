{-
  The image of an ideal under a surjective ring homomorphism is an ideal.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Ring.Ideal.SurjectiveImage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

open import Cubical.Algebra.Ring.Ideal.Base

private
  variable
    ℓ : Level

module _ {R S : Ring ℓ} (f : RingHom R S) (f-epi : isSurjection (fst f)) (I : IdealsIn R) where
  open isIdeal
  open IsRingHom
  open RingStr ⦃...⦄
  private instance _ = snd R
                   _ = snd S

  imageIdeal : IdealsIn S
  fst imageIdeal = λ y → (∃[ x ∈ ⟨ R ⟩ ] (x ∈ fst I) × (fst f x ≡ y)) , isPropPropTrunc
  (snd imageIdeal) .0r-closed     = ∣ 0r , 0r-closed (snd I) , pres0 (snd f) ∣₁
  (snd imageIdeal) .+-closed      =
    rec2 isPropPropTrunc
         λ (x , (x∈I , fx≡-)) (y , (y∈I , fy≡-))
           → ∣ (x + y) , (+-closed (snd I) x∈I y∈I ,
                         (fst f (x + y)     ≡⟨ pres+ (snd f) _ _ ⟩
                          fst f x + fst f y ≡[ i ]⟨ fx≡- i + fy≡- i ⟩
                           _ + _ ∎)) ∣₁

  (snd imageIdeal) .-closed       =
    rec isPropPropTrunc
        λ (x , (x∈I , fx≡-))
          → ∣ (- x) , (-closed (snd I) x∈I ,
                       (fst f (- x) ≡⟨ pres- (snd f) _ ⟩
                        - fst f x   ≡[ i ]⟨ - fx≡- i ⟩
                        (- _) ∎)) ∣₁

  (snd imageIdeal) .·-closedLeft r =
    (rec (isPropΠ (λ _ → isPropPropTrunc))
         λ (s , fs≡r)
           → rec isPropPropTrunc
                 λ (x , (x∈I , fx≡-))
                   → ∣ (s · x) , (·-closedLeft (snd I) s x∈I) ,
                                 (fst f (s · x)     ≡⟨ pres· (snd f) s x ⟩
                                  fst f s · fst f x ≡[ i ]⟨ fs≡r i · fx≡- i ⟩
                                   (r · _) ∎) ∣₁)
    (f-epi r)

  (snd imageIdeal) .·-closedRight r =
    (rec (isPropΠ (λ _ → isPropPropTrunc))
         λ (s , fs≡r)
           → rec isPropPropTrunc
                 λ (x , (x∈I , fx≡-))
                   → ∣ (x · s) , (·-closedRight (snd I) s x∈I) ,
                                 (fst f (x · s)     ≡⟨ pres· (snd f) x s ⟩
                                  fst f x · fst f s ≡[ i ]⟨ fx≡- i · fs≡r i ⟩
                                   (_ · r) ∎) ∣₁)
    (f-epi r)