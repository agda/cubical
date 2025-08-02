module Cubical.Algebra.CommAlgebra.AsModule.Kernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Ideal using (Ideal→CommIdeal)
open import Cubical.Algebra.Ring.Kernel using () renaming (kernelIdeal to ringKernel)
open import Cubical.Algebra.CommAlgebra.AsModule.Base
open import Cubical.Algebra.CommAlgebra.AsModule.Properties
open import Cubical.Algebra.CommAlgebra.AsModule.Ideal

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A B : CommAlgebra R ℓ) (ϕ : CommAlgebraHom A B) where

  kernel : IdealsIn A
  kernel = Ideal→CommIdeal (ringKernel (CommAlgebraHom→RingHom {A = A} {B = B} ϕ))
