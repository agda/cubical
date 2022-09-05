{-# OPTIONS --safe --experimental-lossy-unification #-}

module Cubical.Algebra.CommRing.Instances.IntMod where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup

open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic

open CommRingStr

ℤ/2CommRing : CommRing ℓ-zero
fst ℤ/2CommRing = fst (Group→AbGroup (ℤGroup/ 2) +ₘ-comm)
0r (snd ℤ/2CommRing) = fzero
1r (snd ℤ/2CommRing) = 1
_+_ (snd ℤ/2CommRing) = _+ₘ_
CommRingStr._·_ (snd ℤ/2CommRing) = _·ₘ_
- snd ℤ/2CommRing = -ₘ_
isCommRing (snd ℤ/2CommRing) = is-ring
  where
  abstract
    is-ring : IsCommRing {R = Fin 2} fzero 1 _+ₘ_ _·ₘ_ (-ₘ_)
    is-ring =
      makeIsCommRing
        isSetFin
        (λ x y z → sym (+ₘ-assoc x y z))
        (ℤ/2-elim refl refl)
        (ℤ/2-elim refl refl)
        (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
        (ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
          (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl)))
        (ℤ/2-elim refl refl)
        (ℤ/2-elim (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))
          (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl)))
        (ℤ/2-elim (ℤ/2-elim refl refl) (ℤ/2-elim refl refl))

ℤ/2Ring : Ring ℓ-zero
ℤ/2Ring = CommRing→Ring ℤ/2CommRing
