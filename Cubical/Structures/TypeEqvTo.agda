{-# OPTIONS --cubical --safe #-}
module Cubical.Structures.TypeEqvTo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP renaming (SNS-PathP to SNS)
open import Cubical.Foundations.Pointed
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
  PointedEqvTo-structure = add-to-structure pointed-structure (λ Y _ → ∥ Y ≃ X ∥)

  PointedEqvTo-iso : StrIso PointedEqvTo-structure ℓ''
  PointedEqvTo-iso = add-to-iso pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ X ∥)

  PointedEqvTo-is-SNS : SNS {ℓ} PointedEqvTo-structure PointedEqvTo-iso
  PointedEqvTo-is-SNS = add-axioms-SNS pointed-structure pointed-iso (λ Y _ → ∥ Y ≃ X ∥)
                                       (λ _ _ → squash)
                                       pointed-is-SNS

  PointedEqvTo-SIP : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvTo-iso ] B ≃ (A ≡ B)
  PointedEqvTo-SIP = SIP PointedEqvTo-structure PointedEqvTo-iso PointedEqvTo-is-SNS

  PointedEqvTo-sip : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvTo-iso ] B → (A ≡ B)
  PointedEqvTo-sip A B = equivFun (PointedEqvTo-SIP A B)
