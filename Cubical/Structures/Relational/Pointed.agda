{-

Pointed structure: X ↦ X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Relational.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Structures.Pointed

private
  variable
    ℓ : Level

-- Structured relations

preservesSetsPointed : preservesSets {ℓ = ℓ} PointedStructure
preservesSetsPointed setX = setX

PointedPropRel : StrRel PointedStructure ℓ
PointedPropRel .rel R = R
PointedPropRel .prop propR = propR

open SuitableStrRel
open isQuasiEquivRel

pointedSuitableRel : SuitableStrRel {ℓ = ℓ} PointedStructure PointedPropRel
pointedSuitableRel .quo _ _ _ = isContrSingl _
pointedSuitableRel .symmetric _ r = r
pointedSuitableRel .transitive _ _ r r' = ∣ _ , r , r' ∣

pointedRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} PointedPropRel PointedEquivStr
pointedRelMatchesEquiv _ _ _ = idEquiv _
