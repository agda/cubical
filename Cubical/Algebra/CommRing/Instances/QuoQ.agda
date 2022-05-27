{-

ℚ is a Commutative Ring

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.QuoQ where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.HITs.Rationals.QuoQ
  renaming ( ℚ to ℚType ; _+_ to _+ℚ_; _·_ to _·ℚ_; -_ to -ℚ_)

open CommRingStr

ℚ : CommRing ℓ-zero
fst ℚ = ℚType
0r (snd ℚ) = 0
1r (snd ℚ) = 1
_+_ (snd ℚ) = _+ℚ_
_·_ (snd ℚ) = _·ℚ_
- snd ℚ = -ℚ_
isCommRing (snd ℚ) = isCommRingℚ
  where
  abstract
    isCommRingℚ : IsCommRing 0 1 _+ℚ_ _·ℚ_ -ℚ_
    isCommRingℚ = makeIsCommRing
      isSetℚ +-assoc +-identityʳ
      +-inverseʳ +-comm ·-assoc
      ·-identityʳ (λ x y z → sym (·-distribˡ x y z)) ·-comm
