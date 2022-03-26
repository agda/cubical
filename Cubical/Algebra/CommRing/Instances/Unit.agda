{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

private
  variable
    ℓ : Level

open CommRingStr

UnitCommRing : ∀ {ℓ} → CommRing ℓ
fst UnitCommRing = Unit*
0r (snd UnitCommRing) = tt*
1r (snd UnitCommRing) = tt*
_+_ (snd UnitCommRing) = λ _ _ → tt*
_·_ (snd UnitCommRing) = λ _ _ → tt*
- snd UnitCommRing = λ _ → tt*
isCommRing (snd UnitCommRing) =
  makeIsCommRing isSetUnit* (λ _ _ _ → refl) (λ { tt* → refl }) (λ _ → refl)
                 (λ _ _ → refl) (λ _ _ _ → refl) (λ { tt* → refl })
                 (λ _ _ _ → refl) (λ _ _ → refl)
