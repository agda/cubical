{- ℚ is a CommRing -}

module Cubical.Algebra.CommRing.Instances.Rationals.Fast where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Algebra.CommRing.Instances.Int.Fast
open import Cubical.Data.NatPlusOne.Base
open import Cubical.Data.Nat using (zero)
import Cubical.Data.Int.Fast as ℤ

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

ℤ→ℚCommRingHom : CommRingHom ℤCommRing ℚCommRing
ℤ→ℚCommRingHom .fst x = [ x / 1+ zero ]
ℤ→ℚCommRingHom .snd .IsCommRingHom.pres0 = refl
ℤ→ℚCommRingHom .snd .IsCommRingHom.pres1 = refl
ℤ→ℚCommRingHom .snd .IsCommRingHom.pres+ x y =
 eq/ _ _ (cong (ℤ._· 1) (cong₂ ℤ._+_ (sym (ℤ.·IdR x)) (sym (ℤ.·IdR y))))
ℤ→ℚCommRingHom .snd .IsCommRingHom.pres· _ _ = refl
ℤ→ℚCommRingHom .snd .IsCommRingHom.pres- x =
 eq/ _ _ (cong (ℤ._· 1) (cong (ℤ.-_) (sym (ℤ.·IdL x)) ∙ ℤ.-DistL· 1 x))
