{-# OPTIONS --cubical #-}
module Cubical.Algebra.CommRing.Instances.Pointwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ : Level

pointwiseRing : (X : Type ℓ) (R : CommRing ℓ) → CommRing ℓ
pointwiseRing X R =
  let open CommRingStr (snd R)
      isSetX→R = isOfHLevelΠ 2 (λ _ → isSetCommRing R)
  in (X → fst R) ,
     (commringstr
       (λ _ → 0r) (λ _ → 1r)
       (λ f g → (λ x → f x + g x))
       (λ f g → (λ x → f x · g x))
       (λ f → (λ x → - f x))
       (makeIsCommRing
         isSetX→R
         (λ f g h i x → +Assoc (f x) (g x) (h x) i)
         (λ f i x → +Rid (f x) i)
         (λ f i x → +Rinv (f x) i)
         (λ f g i x → +Comm (f x) (g x) i)
         (λ f g h i x → ·Assoc (f x) (g x) (h x) i)
         (λ f i x → ·Rid (f x) i)
         (λ f g h i x → ·Rdist+ (f x) (g x) (h x) i)
         λ f g i x → ·-comm (f x) (g x) i))
