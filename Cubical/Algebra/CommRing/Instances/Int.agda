{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int as Int
  renaming ( ℤ to ℤType ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

open CommRingStr

ℤ : CommRing ℓ-zero
fst ℤ = ℤType
0r (snd ℤ) = 0
1r (snd ℤ) = 1
_+_ (snd ℤ) = _+ℤ_
_·_ (snd ℤ) = _·ℤ_
- snd ℤ = -ℤ_
isCommRing (snd ℤ) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc (λ _ → refl)
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·Rid ·DistR+ Int.·Comm

