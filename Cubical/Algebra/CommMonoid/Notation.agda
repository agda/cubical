module Cubical.Algebra.CommMonoid.Notation where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.Notation.Additive

private variable
  ℓ : Level

instance
  +CommMonoidProvider : ⦃ A : CommMonoid ℓ ⦄ → AdditiveOperationProvider (fst A)
  +CommMonoidProvider ⦃ A ⦄ = record { _+_ = CommMonoidStr._·_ (snd A) }
