{-

  DUARel for the constant unit family

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Displayed.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Constant

private
  variable
    ℓA ℓ≅A : Level

𝒮-Unit : UARel Unit ℓ-zero
𝒮-Unit .UARel._≅_ _ _ = Unit
𝒮-Unit .UARel.ua _ _ = invEquiv (isContr→≃Unit (isProp→isContrPath isPropUnit _ _))

𝒮ᴰ-Unit : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) → DUARel 𝒮-A (λ _ → Unit) ℓ-zero
𝒮ᴰ-Unit 𝒮-A = 𝒮ᴰ-const 𝒮-A 𝒮-Unit
