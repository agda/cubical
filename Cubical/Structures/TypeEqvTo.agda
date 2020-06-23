{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.TypeEqvTo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP
open import Cubical.Foundations.Pointed
open import Cubical.Structures.Axiom
open import Cubical.Structures.Pointed

private
  variable
    ℓ ℓ' ℓ'' : Level

TypeEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeEqvTo ℓ X = TypeWithStr ℓ (λ Y → ∥ Y ≃ X ∥)

PointedEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
PointedEqvTo ℓ X = TypeWithStr ℓ (λ Y → Y × ∥ Y ≃ X ∥)

module _ (X : Type ℓ') where

  PointedEqvTo-structure : Type ℓ → Type (ℓ-max ℓ ℓ')
  PointedEqvTo-structure = AxiomStructure PointedStructure (λ Y _ → ∥ Y ≃ X ∥)

  PointedEqvTo-iso : StrIso PointedEqvTo-structure ℓ''
  PointedEqvTo-iso = AxiomIso PointedIso (λ Y _ → ∥ Y ≃ X ∥)

  PointedEqvTo-is-SNS : UnivalentStr {ℓ} PointedEqvTo-structure PointedEqvTo-iso
  PointedEqvTo-is-SNS = AxiomUnivalentStr PointedIso {axioms = λ Y _ → ∥ Y ≃ X ∥}
                                          (λ _ _ → squash) PointedUnivalentStr

  PointedEqvTo-SIP : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvTo-iso ] B ≃ (A ≡ B)
  PointedEqvTo-SIP = SIP PointedEqvTo-is-SNS

  PointedEqvTo-sip : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvTo-iso ] B → (A ≡ B)
  PointedEqvTo-sip A B = equivFun (PointedEqvTo-SIP A B)
