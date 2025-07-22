{-
  The image of an ideal under a surjective ring homomorphism is an ideal.
  (imported from Ring.Ideal.SurjectiveImage)
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Ideal.SurjectiveImage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring.Base using (IsRingHom)
import Cubical.Algebra.Ring.Ideal.SurjectiveImage as Ring
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Ideal.Base

private
  variable
    ℓ : Level

open CommIdeal

imageIdeal : {R S : CommRing ℓ}   -- same universe level is needed with our definition of ideals
             (f : CommRingHom R S) (f-epi : isSurjection (fst f))
             (I : IdealsIn R)
              → IdealsIn S
imageIdeal f f-epi I = Ideal→CommIdeal (Ring.imageIdeal (CommRingHom→RingHom f) f-epi (CommIdeal→Ideal I))

image0Ideal : {R S : CommRing ℓ} (f : CommRingHom R S) (f-epi : isSurjection (fst f))
              → imageIdeal f f-epi (0Ideal R) ≡ (0Ideal S)
image0Ideal f f-epi = Σ≡Prop (isPropIsCommIdeal _) (cong fst $ Ring.image0Ideal (CommRingHom→RingHom f) f-epi)
