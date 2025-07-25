{-

Constant structure: _ ↦ A

-}
module Cubical.Structures.Relational.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Structures.Constant

private
  variable
    ℓ ℓ' : Level

-- Structured relations

module _ (A : hSet ℓ') where

  ConstantRelStr : StrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ℓ'
  ConstantRelStr _ a₀ a₁ = a₀ ≡ a₁

  constantSuitableRel : SuitableStrRel {ℓ = ℓ} (ConstantStructure (A .fst)) ConstantRelStr
  constantSuitableRel .quo _ _ _ = isContrSingl _
  constantSuitableRel .symmetric _ = sym
  constantSuitableRel .transitive _ _ = _∙_
  constantSuitableRel .set _ = A .snd
  constantSuitableRel .prop _ = A .snd

  constantRelMatchesEquiv : StrRelMatchesEquiv {ℓ = ℓ} ConstantRelStr (ConstantEquivStr (A .fst))
  constantRelMatchesEquiv _ _ _ = idEquiv _

  constantRelAction : StrRelAction {ℓ = ℓ} ConstantRelStr
  constantRelAction .actStr _ a = a
  constantRelAction .actStrId _ = refl
  constantRelAction .actRel _ a a' p = p

  constantPositiveRel : PositiveStrRel {ℓ = ℓ} constantSuitableRel
  constantPositiveRel .act = constantRelAction
  constantPositiveRel .reflexive a = refl
  constantPositiveRel .detransitive R R' p = ∣ _ , p , refl ∣₁
  constantPositiveRel .quo R = isoToIsEquiv isom
    where
    open Iso
    isom : Iso _ _
    isom .fun = _
    isom .inv = [_]
    isom .rightInv _ = refl
    isom .leftInv = elimProp (λ _ → squash/ _ _) (λ a → refl)
