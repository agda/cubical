{-

ℚ is a Commutative Ring

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.QuoQ where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.HITs.Rationals.QuoQ
  renaming (ℚ to ℚType ; _+_ to _+ℚ_; _·_ to _·ℚ_; -_ to -ℚ_)

open CommRingStr


ℚCommRing : CommRing ℓ-zero
ℚCommRing .fst = ℚType
ℚCommRing .snd .0r = 0
ℚCommRing .snd .1r = 1
ℚCommRing .snd ._+_ = _+ℚ_
ℚCommRing .snd ._·_ = _·ℚ_
ℚCommRing .snd .-_ = -ℚ_
ℚCommRing .snd .isCommRing = isCommRingℚ
  where
  abstract
    isCommRingℚ : IsCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_
    isCommRingℚ = makeIsCommRing
      isSetℚ +-assoc +-identityʳ
      +-inverseʳ +-comm ·-assoc
      ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm
