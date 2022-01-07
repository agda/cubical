{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.Kernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Properties
open import Cubical.Algebra.CommAlgebra.Ideal

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} {A B : CommAlgebra R ℓ} (ϕ : CommAlgebraHom A B) where

  kernel : IdealsIn A
  kernel = ?
