{-
  The image of an ideal under a surjective ring homomorphism is an ideal.
  (imported from Ring.Ideal.SurjectiveImage)
-}
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
             (f : CommRingHom R S) (f-surjective : isSurjection (fst f))
             (I : IdealsIn R)
              → IdealsIn S
imageIdeal f f-surjective I = Ideal→CommIdeal (Ring.imageIdeal (CommRingHom→RingHom f) f-surjective (CommIdeal→Ideal I))

image0Ideal : {R S : CommRing ℓ} (f : CommRingHom R S) (f-surjective : isSurjection (fst f))
              → imageIdeal f f-surjective (0Ideal R) ≡ (0Ideal S)
image0Ideal f f-surjective = Σ≡Prop (isPropIsCommIdeal _) (cong fst $ Ring.image0Ideal (CommRingHom→RingHom f) f-surjective)
