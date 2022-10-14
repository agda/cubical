{-
  The image of an ideal under a surjective ring homomorphism is an ideal.
  (imported from Ring.Ideal.SurjectiveImage)
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal.SurjectiveImage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Surjection

open import Cubical.Algebra.Ring.Base using (IsRingHom)
import Cubical.Algebra.Ring.Ideal.SurjectiveImage as Ring
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Ideal.Base

private
  variable
    ℓ : Level

imageIdeal : {R S : CommRing ℓ}
             (f : CommRingHom R S) (f-epi : isSurjection (fst f))
             (I : IdealsIn R)
              → IdealsIn S
imageIdeal f f-epi I = Ideal→CommIdeal (Ring.imageIdeal f f-epi (CommIdeal→Ideal I))
