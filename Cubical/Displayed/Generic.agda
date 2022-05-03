{-

  Generic UARel, DUARel, and SubstRel: the path relation is always univalent

-}
{-# OPTIONS --safe #-}
module Cubical.Displayed.Generic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- UARel for an arbitrary type

𝒮-generic : (A : Type ℓA) → UARel A ℓA
UARel._≅_ (𝒮-generic A) = _≡_
UARel.ua (𝒮-generic A) a a' = idEquiv (a ≡ a')

-- DUARel for an arbitrary family

𝒮ᴰ-generic : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB) → DUARel 𝒮-A B ℓB
𝒮ᴰ-generic 𝒮-A B .DUARel._≅ᴰ⟨_⟩_ b p b' = PathP (λ i → B (UARel.≅→≡ 𝒮-A p i)) b b'
𝒮ᴰ-generic 𝒮-A B .DUARel.uaᴰ b p b' = idEquiv _

-- SubstRel for an arbitrary family

𝒮ˢ-generic : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (B : A → Type ℓB) → SubstRel 𝒮-A B
𝒮ˢ-generic 𝒮-A B .SubstRel.act p = substEquiv B (UARel.≅→≡ 𝒮-A p)
𝒮ˢ-generic 𝒮-A B .SubstRel.uaˢ p b = refl
