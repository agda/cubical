{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Structures.Type where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit

open import Cubical.Displayed.Base
open import Cubical.Displayed.Properties

private
  variable
    ℓ ℓA ℓ≅A ℓP : Level

𝒮-type : (A : Type ℓ) → UARel A ℓ
UARel._≅_ (𝒮-type A) = _≡_
UARel.ua (𝒮-type A) a a' = idEquiv (a ≡ a')

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) where
  𝒮ᴰ-subtype : (P : A → hProp ℓP) → DUARel 𝒮-A (λ a → P a .fst) ℓ-zero
  DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-subtype P) _ _ _ = Unit
  DUARel.uaᴰ (𝒮ᴰ-subtype P) p q p' = {!!}


𝒮-uniqueness : (A : Type ℓA) → isContr (UARel A ℓA)
𝒮-uniqueness A .fst = 𝒮-type A
𝒮-uniqueness A .snd 𝒮' = {!!}
