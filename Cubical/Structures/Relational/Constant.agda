{-

Constant structure: _ ↦ A

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure

open import Cubical.Structures.Constant

private
  variable
    ℓ ℓ' : Level

-- Structured relations

module _ (A : hSet ℓ') where

  preservesSetsConstant : preservesSets {ℓ = ℓ} (ConstantStructure (A .fst))
  preservesSetsConstant _ = A .snd

  ConstantPropRel : StrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ℓ'
  ConstantPropRel .rel _ a₀ a₁ = a₀ ≡ a₁
  ConstantPropRel .prop _ = A .snd

  open SuitableStrRel

  constantSuitableRel : SuitableStrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ConstantPropRel
  constantSuitableRel .quo _ _ _ = isContrSingl _
  constantSuitableRel .symmetric _ = sym
  constantSuitableRel .transitive _ _ = _∙_

  constantRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} ConstantPropRel (ConstantEquivStr (A .fst))
  constantRelMatchesEquiv _ _ _ = idEquiv _
