{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Algebra.CommRing.Instances.IntMod where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic

open CommRingStr
open IsCommRing
open IsMonoid
open IsSemigroup
open IsRing
open AbGroupStr

ℤ/2CommRing : CommRing ℓ-zero
fst ℤ/2CommRing = fst (Group→AbGroup (ℤGroup/ 2) +ₘ-comm)
0r (snd ℤ/2CommRing) = fzero
1r (snd ℤ/2CommRing) = 1
_+_ (snd ℤ/2CommRing) = _+ₘ_
CommRingStr._·_ (snd ℤ/2CommRing) = _·ₘ_
CommRingStr.- snd ℤ/2CommRing = -ₘ_
+IsAbGroup (isRing (isCommRing (snd ℤ/2CommRing))) =
  isAbGroup (Group→AbGroup (ℤGroup/ 2) +ₘ-comm .snd)
is-set (isSemigroup (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing))))) = isSetFin
IsSemigroup.·Assoc (isSemigroup (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing))))) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
·IdR (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing)))) = ℤ/2-elim refl refl
·IdL (·IsMonoid (isRing (isCommRing (snd ℤ/2CommRing)))) = ℤ/2-elim refl refl
IsRing.·DistR+ (isRing (isCommRing (snd ℤ/2CommRing))) =
  ℤ/2-elim (λ y z → refl) (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsRing.·DistL+ (isRing (isCommRing (snd ℤ/2CommRing))) =
  ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
  (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
IsCommRing.·Comm (isCommRing (snd ℤ/2CommRing)) =
  ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl)

ℤ/2Ring : Ring ℓ-zero
ℤ/2Ring = CommRing→Ring ℤ/2CommRing
