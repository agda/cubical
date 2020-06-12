{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.ProperField where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_; isProp¬)
open import Cubical.Structures.CommRing
open import Cubical.Structures.Field


private
  variable
    ℓ : Level

module _ (R : CommRing {ℓ}) where
  open comm-ring-syntax R

  isProperField : Type ℓ
  isProperField = (¬ 0r ≡ 1r) × (nonZeroElementsAreInvertible R (denialInequality R))

  isPropIsProperField : isProp (isProperField)
  isPropIsProperField = isPropΣ (isProp¬ _)
                                λ _ → (isPropNonZeroElementsInvertible R (denialInequality R))

private
  properFieldAxioms : (R : Type ℓ) → comm-ring-structure R → Type ℓ
  properFieldAxioms R cringStr = isProperField (R , cringStr)

  properFieldAxioms-isProp : (R : Type ℓ) → (cringStr : comm-ring-structure R)
                             → isProp (properFieldAxioms R cringStr)
  properFieldAxioms-isProp R cringStr = isPropIsProperField (R , cringStr)

properFieldStructure : Type ℓ → Type ℓ
properFieldStructure = add-to-structure comm-ring-structure properFieldAxioms

ProperField : Type (ℓ-suc ℓ)
ProperField {ℓ} = TypeWithStr ℓ properFieldStructure

properFieldIso : StrIso properFieldStructure ℓ
properFieldIso = add-to-iso comm-ring-iso properFieldAxioms

properFieldIsSNS : SNS {ℓ} properFieldStructure properFieldIso
properFieldIsSNS = add-axioms-SNS _ properFieldAxioms-isProp comm-ring-is-SNS

ProperFieldPath : (K L : ProperField {ℓ}) → (K ≃[ properFieldIso ] L) ≃ (K ≡ L)
ProperFieldPath = SIP properFieldIsSNS
