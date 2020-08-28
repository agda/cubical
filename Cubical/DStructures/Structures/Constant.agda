{-
This module contains:
- constant displayed structures of URG structures
- products of URG structures
-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties

open import Cubical.Relation.Binary

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅C ℓ≅A×B : Level

-- The constant displayed structure of a URG structure 𝒮-B over 𝒮-A
𝒮ᴰ-const : {A : Type ℓA} (𝒮-A : URGStr A ℓ≅A)
               {B : Type ℓB} (𝒮-B : URGStr B ℓ≅B)
               → URGStrᴰ 𝒮-A (λ _ → B) ℓ≅B
𝒮ᴰ-const {A = A} 𝒮-A {B} 𝒮-B
  = urgstrᴰ (λ b _ b' → b ≅ b') ρ uni
    where
      open URGStr 𝒮-B

-- the total structure of the constant structure gives
-- nondependent product of URG structures
_×𝒮_ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
         {B : Type ℓB} (StrB : URGStr B ℓ≅B)
         → URGStr (A × B) (ℓ-max ℓ≅A ℓ≅B)
_×𝒮_ StrA {B} StrB = ∫⟨ StrA ⟩ (𝒮ᴰ-const StrA StrB)

-- any displayed structure defined over a
-- structure on a product can also be defined
-- over the swapped product
×𝒮-swap :  {A : Type ℓA} {B : Type ℓB} {C : A × B → Type ℓC}
         {ℓ≅A×B ℓ≅ᴰ : Level}
         {StrA×B : URGStr (A × B) ℓ≅A×B}
         (StrCᴰ : URGStrᴰ StrA×B C ℓ≅ᴰ)
         → URGStrᴰ (𝒮-transport Σ-swap-≃ StrA×B)
                   (λ (b , a) → C (a , b))
                   ℓ≅ᴰ
×𝒮-swap {C = C} {ℓ≅ᴰ = ℓ≅ᴰ} {StrA×B = StrA×B} StrCᴰ =
  make-𝒮ᴰ (λ c p c' → c ≅ᴰ⟨ p ⟩ c')
              ρᴰ
              λ (b , a) c → isUnivalent→contrRelSingl (λ c c' → c ≅ᴰ⟨ URGStr.ρ StrA×B (a , b) ⟩ c')
                                                        ρᴰ
                                                        uniᴰ
                                                        c
              where
                open URGStrᴰ StrCᴰ
