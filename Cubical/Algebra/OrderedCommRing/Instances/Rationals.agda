module Cubical.Algebra.OrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.StrictOrder.Instances.Rationals

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.Pseudolattice.Instances.Rationals

open CommRingStr
open OrderedCommRingStr
open PseudolatticeStr
open StrictOrderStr

ℚOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℚOrderedCommRing = ℚ
0r  (snd ℚOrderedCommRing) = 0
1r  (snd ℚOrderedCommRing) = 1
_+_ (snd ℚOrderedCommRing) = _+ℚ_
_·_ (snd ℚOrderedCommRing) = _·ℚ_
-_  (snd ℚOrderedCommRing) = -ℚ_
_<_ (snd ℚOrderedCommRing) = _<ℚ_
_≤_ (snd ℚOrderedCommRing) = _≤ℚ_
isOrderedCommRing (snd ℚOrderedCommRing) = isOrderedCommRingℚ
  where
  open IsOrderedCommRing

  isOrderedCommRingℚ : IsOrderedCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedCommRingℚ .isCommRing      = ℚCommRing .snd .isCommRing
  isOrderedCommRingℚ .isPseudolattice = ℚ≤Pseudolattice .snd .is-pseudolattice
  isOrderedCommRingℚ .isStrictOrder   = ℚ<StrictOrder .snd .isStrictOrder
  isOrderedCommRingℚ .<-≤-weaken      = <Weaken≤
  isOrderedCommRingℚ .≤≃¬>            = λ x y →
    propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <ℚ x)) (≤→≯  x y) (≮→≥ y x)
  isOrderedCommRingℚ .+MonoR≤         = ≤-+o
  isOrderedCommRingℚ .+MonoR<         = <-+o
  isOrderedCommRingℚ .posSum→pos∨pos  = λ x y → ∣_∣₁ ∘ 0<+ x y
  isOrderedCommRingℚ .<-≤-trans       = isTrans<≤
  isOrderedCommRingℚ .≤-<-trans       = isTrans≤<
  isOrderedCommRingℚ .·MonoR≤         = ≤-·o
  isOrderedCommRingℚ .·MonoR<         = <-·o
  isOrderedCommRingℚ .0<1             = pos<pos tt
