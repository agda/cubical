module Cubical.Algebra.CommRing.Kernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Ideal using (IdealsIn; Ideal→CommIdeal)
open import Cubical.Algebra.Ring.Kernel using () renaming (kernelIdeal to ringKernelIdeal; kernelFiber to ringKernelFiber)

private
  variable
    ℓ : Level


module _ (R S : CommRing ℓ) (f : CommRingHom R S) where
  open CommRingStr (snd R)

  -- If R and S were implicit, their ·Comm component could (almost?) never be inferred.
  kernelIdeal : IdealsIn R
  kernelIdeal = Ideal→CommIdeal (ringKernelIdeal (CommRingHom→RingHom f))

  kernelFiber : (x y : ⟨ R ⟩) → fst f x ≡ fst f y → (x - y) ∈ fst kernelIdeal
  kernelFiber x y p = ringKernelFiber (CommRingHom→RingHom f) x y p
