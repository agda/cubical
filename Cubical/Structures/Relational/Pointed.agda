{-

Pointed structure: X ↦ X

-}
{-# OPTIONS --safe #-}
module Cubical.Structures.Relational.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
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

PointedRelStr : StrRel PointedStructure ℓ
PointedRelStr R = R

pointedSuitableRel : SuitableStrRel {ℓ = ℓ} PointedStructure PointedRelStr
pointedSuitableRel .quo _ _ _ = isContrSingl _
pointedSuitableRel .symmetric _ r = r
pointedSuitableRel .transitive _ _ r r' = ∣ _ , r , r' ∣
pointedSuitableRel .set setX = setX
pointedSuitableRel .prop propR = propR

pointedRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} PointedRelStr PointedEquivStr
pointedRelMatchesEquiv _ _ _ = idEquiv _

pointedRelAction : StrRelAction {ℓ = ℓ} PointedRelStr
pointedRelAction .actStr f = f
pointedRelAction .actStrId _ = refl
pointedRelAction .actRel α = α

pointedPositiveRel : PositiveStrRel {ℓ = ℓ} pointedSuitableRel
pointedPositiveRel .act = pointedRelAction
pointedPositiveRel .reflexive x = ∣ refl ∣
pointedPositiveRel .detransitive R R' rr' = rr'
pointedPositiveRel .quo R = isoToIsEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = _
  isom .inv q = q
  isom .rightInv = elimProp (λ _ → squash/ _ _) (λ _ → refl)
  isom .leftInv = elimProp (λ _ → squash/ _ _) (λ _ → refl)
