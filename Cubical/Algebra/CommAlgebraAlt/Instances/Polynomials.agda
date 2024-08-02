{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.Instances.Polynomials where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommAlgebraAlt.Base
open import Cubical.Algebra.CommRing.Instances.Polynomials.Typevariate

private
  variable
    ℓ ℓ' : Level

_[_] : (R : CommRing ℓ) (I : Type ℓ') → CommAlgebra R _
R [ I ] = (R [ I ]ᵣ) , const R I
