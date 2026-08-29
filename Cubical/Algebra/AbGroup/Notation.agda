{-# OPTIONS --safe #-}
module Cubical.Algebra.AbGroup.Notation where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Notation.Additive

private variable
  ℓ : Level

instance
  +AbGroupProvider : ⦃ A : AbGroup ℓ ⦄ → AdditiveOperationProvider (fst A)
  +AbGroupProvider ⦃ A ⦄ = record { _+_ = AbGroupStr._+_ (snd A) }
