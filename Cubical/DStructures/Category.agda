
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Data.Sigma

open import Cubical.DStructures.DispSIP
open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Categories.Category renaming (isUnivalent to isUnivalentCat)

private
  variable
    ℓ ℓ' ℓ'' ℓ₁ ℓ₁' ℓ₁'' ℓ₂ ℓA ℓ≅A ℓB ℓ≅B ℓ≅ᴰ : Level

-- every univalent 1-precategory gives a URGStr
Cat→URG : (𝒞 : Precategory ℓ ℓ') → (uni : isUnivalentCat 𝒞) → URGStr (𝒞 .ob) ℓ'
Cat→URG 𝒞 uni
  = urgstr (CatIso {𝒞 = 𝒞}) idCatIso λ x y → isUnivalentCat.univ uni x y
