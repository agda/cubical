{-# OPTIONS --safe #-}
module Cubical.Algebra.RingSolver.CommRingAsAlmostRing where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Ring.Properties

private
  variable
    ℓ : Level

open Cubical.Algebra.Ring.Properties.RingTheory

CommRingAsAlmostRing : CommRing ℓ → AlmostRing ℓ
CommRingAsAlmostRing {ℓ}
  (R , commringstr _ _ _ _ _
         (iscommring (isring
                       (isabgroup (isgroup +-isMonoid inverse) +-comm)
                       ·-isMonoid dist)
                     ·-comm)) =
  let
    R' : CommRing ℓ
    R' = (R , commringstr _ _ _ _ _
         (iscommring (isring
                       (isabgroup (isgroup +-isMonoid inverse) +-comm) ·-isMonoid dist)
                     ·-comm))
    R″ = CommRing→Ring R'
  in almostring R _ _ _ _ _
     (isalmostring
       +-isMonoid
       ·-isMonoid
       +-comm
       ·-comm
       (λ x y z → fst (dist x y z))
       (λ x y z → snd (dist x y z))
       (λ x y → sym (-DistL· R″ x y))
       (λ x y → sym (-Dist R″ x y))
       (λ x → 0LeftAnnihilates R″ x)
       λ x → 0RightAnnihilates R″ x)
