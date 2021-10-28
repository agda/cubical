{-

  - UARel given by a universe and equivalences
  - SubstRel and DUARel for the element family over the universe

-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Displayed.Universe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Displayed.Base
open import Cubical.Displayed.Subst

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B ℓP : Level

𝒮-Univ : ∀ ℓ → UARel (Type ℓ) ℓ
𝒮-Univ ℓ .UARel._≅_ = _≃_
𝒮-Univ ℓ .UARel.ua _ _ = isoToEquiv (invIso univalenceIso)

𝒮ˢ-El : ∀ ℓ → SubstRel (𝒮-Univ ℓ) (λ X → X)
𝒮ˢ-El ℓ .SubstRel.act e = e
𝒮ˢ-El ℓ .SubstRel.uaˢ e a = uaβ e a

𝒮ᴰ-El : ∀ ℓ → DUARel (𝒮-Univ ℓ) (λ X → X) ℓ
𝒮ᴰ-El ℓ .DUARel._≅ᴰ⟨_⟩_  a e a' = e .fst a ≡ a'
𝒮ᴰ-El ℓ .DUARel.uaᴰ a e a' = invEquiv (ua-ungluePath-Equiv e)
