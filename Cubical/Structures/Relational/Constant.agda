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

  ConstantRelStr : StrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ℓ'
  ConstantRelStr _ a₀ a₁ = a₀ ≡ a₁

  open SuitableStrRel

  constantSuitableRel : SuitableStrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ConstantRelStr
  constantSuitableRel .quo _ _ _ = isContrSingl _
  constantSuitableRel .symmetric _ = sym
  constantSuitableRel .transitive _ _ = _∙_
  constantSuitableRel .set _ = A .snd
  constantSuitableRel .prop _ = A .snd

  constantRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} ConstantRelStr (ConstantEquivStr (A .fst))
  constantRelMatchesEquiv _ _ _ = idEquiv _
