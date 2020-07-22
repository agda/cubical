
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Category where

open import Cubical.Foundations.Prelude

open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

open import Cubical.Categories.Category renaming (isUnivalent to isUnivalentCat)

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

-- every univalent 1-precategory gives a URGStr
Cat→𝒮 : (𝒞 : Precategory ℓ ℓ') → (uni : isUnivalentCat 𝒞) → URGStr (𝒞 .ob) ℓ'
Cat→𝒮 𝒞 uni
  = urgstr (CatIso {𝒞 = 𝒞}) idCatIso λ x y → isUnivalentCat.univ uni x y
