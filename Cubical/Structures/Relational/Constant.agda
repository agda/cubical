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

  ConstantSetStructure : SetStructure ℓ ℓ'
  ConstantSetStructure .struct = ConstantStructure (A .fst)
  ConstantSetStructure .set _ = A .snd

  ConstantPropRel : StrRel {ℓ = ℓ} (ConstantSetStructure .struct) ℓ'
  ConstantPropRel .rel _ a₀ a₁ = a₀ ≡ a₁
  ConstantPropRel .prop _ = A .snd

  open isUnivalentRel
  open BisimDescends

  constantUnivalentRel : isUnivalentRel {ℓ = ℓ} ConstantSetStructure ConstantPropRel
  constantUnivalentRel .propQuo R = isContr→isProp (isContrSingl _)
  constantUnivalentRel .descends _ .fst _ .quoᴸ = (_ , refl)
  constantUnivalentRel .descends _ .fst _ .quoᴿ = (_ , refl)
  constantUnivalentRel .descends _ .fst r .path = r
  constantUnivalentRel .descends _ .snd d = d .quoᴸ .snd ∙∙ d .path ∙∙ sym (d .quoᴿ .snd)

