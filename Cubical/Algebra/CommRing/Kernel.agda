{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.Kernel where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Ideal using (IdealsIn; Ideal→CommIdeal)
open import Cubical.Algebra.Ring.Kernel using () renaming (kernelIdeal to ringKernelIdeal)

private
  variable
    ℓ : Level

kernelIdeal : {R S : CommRing ℓ} (f : CommRingHom R S) → IdealsIn R
kernelIdeal f = Ideal→CommIdeal (ringKernelIdeal f)
