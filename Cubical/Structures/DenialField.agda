{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.DenialField where

{-
  Definition of a denial field following
  Mines, Richman and Ruitenburg, "A Course in Constructive Algebra" (1988)

  A denial field is a commutative ring such that every element which is not equal to zero has
  a multiplicative inverse AND if a product is zero, a factor must be zero.
  NOTE that the zero ring is not excluded by this definition.
-}

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic using ([_])
open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_; isProp¬)
open import Cubical.Structures.CommRing
open import Cubical.Structures.Field
open import Cubical.Structures.Ideal
open import Cubical.Structures.PrimeIdeal

private
  variable
    ℓ : Level

module _ (R : CommRing {ℓ}) where
  open commring-·syntax R

  zeroIdealIsPrime : hProp _
  zeroIdealIsPrime = isPrimeIdeal (CommRing→Ring R) (zeroIdeal (CommRing→Ring R))

  isDenialField : Type ℓ
  isDenialField = [ zeroIdealIsPrime ] × (nonZeroElementsAreInvertible R (denialInequality R))

  isPropIsDenialField : isProp (isDenialField)
  isPropIsDenialField = isPropΣ (snd zeroIdealIsPrime) λ _ → (isPropNonZeroElementsInvertible R (denialInequality R))

private
  denialFieldAxioms : (R : Type ℓ) → comm-ring-structure R → Type ℓ
  denialFieldAxioms R cringStr = isDenialField (R , cringStr)

  denialFieldAxioms-isProp : (R : Type ℓ) → (cringStr : comm-ring-structure R)
                             → isProp (denialFieldAxioms R cringStr)
  denialFieldAxioms-isProp R cringStr = isPropIsDenialField (R , cringStr)

denialFieldStructure : Type ℓ → Type ℓ
denialFieldStructure = add-to-structure comm-ring-structure denialFieldAxioms

DenialField : Type (ℓ-suc ℓ)
DenialField {ℓ} = TypeWithStr ℓ denialFieldStructure

denialFieldIso : StrIso denialFieldStructure ℓ
denialFieldIso = add-to-iso comm-ring-iso denialFieldAxioms

denialFieldIsSNS : SNS {ℓ} denialFieldStructure denialFieldIso
denialFieldIsSNS = add-axioms-SNS _ denialFieldAxioms-isProp comm-ring-is-SNS

DenialFieldPath : (K L : DenialField {ℓ}) → (K ≃[ denialFieldIso ] L) ≃ (K ≡ L)
DenialFieldPath = SIP denialFieldIsSNS
