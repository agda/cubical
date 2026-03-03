{-

ℚ is a CommRing

-}
module Cubical.Algebra.CommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ

ℚCommRing : CommRing ℓ-zero
ℚCommRing .fst = ℚ
ℚCommRing .snd .CommRingStr.0r = 0
ℚCommRing .snd .CommRingStr.1r = 1
ℚCommRing .snd .CommRingStr._+_ = _+_
ℚCommRing .snd .CommRingStr._·_ = _·_
ℚCommRing .snd .CommRingStr.-_  = -_
ℚCommRing .snd .CommRingStr.isCommRing = p
  where
  p : IsCommRing 0 1 _+_ _·_ (-_)
  p = makeIsCommRing isSetℚ +Assoc +IdR +InvR +Comm ·Assoc ·IdR ·DistL+ ·Comm

