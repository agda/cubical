{-

Constant structure: _ ↦ A

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.RelationalStructure

open import Cubical.Structures.Constant

private
  variable
    ℓ ℓ' : Level

-- Structured relations

module _ (A : hSet ℓ') where

  constant-setStructure : SetStructure ℓ ℓ'
  constant-setStructure .struct = ConstantStructure (A .fst)
  constant-setStructure .set _ = A .snd

  constant-propRel : StrRel {ℓ = ℓ} (constant-setStructure .struct) ℓ'
  constant-propRel .rel _ a₀ a₁ = a₀ ≡ a₁
  constant-propRel .prop _ = A .snd

  open isSNRS
  open BisimDescends

  isSNRSConstant : isSNRS {ℓ = ℓ} constant-setStructure constant-propRel
  isSNRSConstant .propQuo R = isContr→isProp (isContrSingl _)
  isSNRSConstant .descends _ .fst _ .quoᴸ = (_ , refl)
  isSNRSConstant .descends _ .fst _ .quoᴿ = (_ , refl)
  isSNRSConstant .descends _ .fst r .path = r
  isSNRSConstant .descends _ .snd d = d .quoᴸ .snd ∙∙ d .path ∙∙ sym (d .quoᴿ .snd)

