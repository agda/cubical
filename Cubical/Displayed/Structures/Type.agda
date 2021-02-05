{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Structures.Type where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

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
  𝒮ᴰ-subtype P
    = make-𝒮ᴰ-2 (λ _ _ _ → Unit)
                (λ _ → tt)
                λ a p → isOfHLevelRespectEquiv 0
                                               (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                               (inhProp→isContr p (P a .snd))

