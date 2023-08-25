{-

  Provides an instance-dependent '_+_'

-}

module Cubical.Algebra.Notation.Additive where

open import Cubical.Foundations.Prelude

private variable
  ℓ : Level

record AdditiveOperationProvider (A : Type ℓ) : Type ℓ where
  field
    _+_ : A → A → A

_+_ : {A : Type ℓ} ⦃ provider : AdditiveOperationProvider A ⦄ → A → A → A
_+_ {A = A} ⦃ provider ⦄ = AdditiveOperationProvider._+_ provider
