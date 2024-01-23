{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int as Int
  renaming ( ℤ to ℤ ; _+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)

ℤCommRing : CommRing ℓ-zero
fst ℤCommRing = ℤ
0r (snd ℤCommRing) = 0
1r (snd ℤCommRing) = 1
_+_ (snd ℤCommRing) = _+ℤ_
_·_ (snd ℤCommRing) = _·ℤ_
- snd ℤCommRing = -ℤ_
isCommRing (snd ℤCommRing) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing 0 1 _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc (λ _ → refl)
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·IdR ·DistR+ Int.·Comm
