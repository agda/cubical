{-

  DUARel for the constant unit family

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Displayed.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Displayed.Base

private
  variable
    ℓA ℓ≅A : Level

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) where

  𝒮ᴰ-Unit : DUARel 𝒮-A (λ _ → Unit) ℓ-zero
  DUARel._≅ᴰ⟨_⟩_ 𝒮ᴰ-Unit _ _ _ = Unit
  DUARel.uaᴰ 𝒮ᴰ-Unit u _ u' =
    invEquiv (isContr→≃Unit (isProp→isContrPath isPropUnit u u'))
