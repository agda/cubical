{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

open import Cubical.Relation.Binary
open BinaryRelation

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B ℓC ℓ≅A×B : Level

-- The constant structure over a structure
URGStrConstᴰ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
               {B : Type ℓB} (StrB : URGStr B ℓ≅B)
               → URGStrᴰ StrA (λ _ → B) ℓ≅B
URGStrConstᴰ {A = A} StrA {B} StrB
  = urgstrᴰ (λ b _ b' → b ≅ b') ρ uni
    where
      open URGStr StrB

-- the total structure of the constant structure gives nondependent product
_×URG_ : {A : Type ℓA} (StrA : URGStr A ℓ≅A)
         {B : Type ℓB} (StrB : URGStr B ℓ≅B)
         → URGStr (A × B) (ℓ-max ℓ≅A ℓ≅B)
_×URG_ StrA {B} StrB = ∫⟨ StrA ⟩ (URGStrConstᴰ StrA StrB)

×URG-swap :  {A : Type ℓA} {B : Type ℓB} {C : A × B → Type ℓC}
         {ℓ≅A×B ℓ≅ᴰ : Level}
         {StrA×B : URGStr (A × B) ℓ≅A×B}
         (StrCᴰ : URGStrᴰ StrA×B C ℓ≅ᴰ)
         → URGStrᴰ (URGStr-transport Σ-swap-≃ StrA×B)
                   (λ (b , a) → C (a , b))
                   ℓ≅ᴰ
×URG-swap {C = C} {ℓ≅ᴰ = ℓ≅ᴰ} {StrA×B = StrA×B} StrCᴰ =
  makeURGStrᴰ (λ c p c' → c ≅ᴰ⟨ p ⟩ c')
              ρᴰ
              λ (b , a) c → isUnivalent→contrTotalSpace (λ c c' → c ≅ᴰ⟨ URGStr.ρ StrA×B (a , b) ⟩ c')
                                                        ρᴰ
                                                        uniᴰ
                                                        c
              where
                open URGStrᴰ StrCᴰ
