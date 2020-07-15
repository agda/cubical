{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.DStructures.Base
open import Cubical.DStructures.Properties

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B : Level

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
