{-

  Functions building DUARels on constant families

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- constant DUARel

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)  where

  open UARel 𝒮-B
  open DUARel

  𝒮ᴰ-const : DUARel 𝒮-A (λ _ → B) ℓ≅B
  𝒮ᴰ-const ._≅ᴰ⟨_⟩_ b _ b' = b ≅ b'
  𝒮ᴰ-const .uaᴰ b p b' = ua b b'

-- SubstRel for an arbitrary constant family

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (B : Type ℓB) where

  open SubstRel

  𝒮ˢ-const : SubstRel 𝒮-A (λ _ → B)
  𝒮ˢ-const .SubstRel.act _ = idEquiv B
  𝒮ˢ-const .SubstRel.uaˢ p b = transportRefl b
