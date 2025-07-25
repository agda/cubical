module Cubical.Data.Unit.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base

open import Cubical.Data.Unit

private
  variable
    ℓ : Level

Unit∙ : Pointed ℓ
Unit∙ = Unit* , tt*
