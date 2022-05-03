{-# OPTIONS --safe #-}
module Cubical.Structures.TypeEqvTo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP
open import Cubical.Foundations.Pointed
open import Cubical.Structures.Axioms
open import Cubical.Structures.Pointed

private
  variable
    ℓ ℓ' ℓ'' : Level

TypeEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
TypeEqvTo ℓ X = TypeWithStr ℓ (λ Y → ∥ Y ≃ X ∥)

PointedEqvTo : (ℓ : Level) (X : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
PointedEqvTo ℓ X = TypeWithStr ℓ (λ Y → Y × ∥ Y ≃ X ∥)

module _ (X : Type ℓ') where

  PointedEqvToStructure : Type ℓ → Type (ℓ-max ℓ ℓ')
  PointedEqvToStructure = AxiomsStructure PointedStructure (λ Y _ → ∥ Y ≃ X ∥)

  PointedEqvToEquivStr : StrEquiv PointedEqvToStructure ℓ''
  PointedEqvToEquivStr = AxiomsEquivStr PointedEquivStr (λ Y _ → ∥ Y ≃ X ∥)

  pointedEqvToUnivalentStr : UnivalentStr {ℓ} PointedEqvToStructure PointedEqvToEquivStr
  pointedEqvToUnivalentStr = axiomsUnivalentStr PointedEquivStr {axioms = λ Y _ → ∥ Y ≃ X ∥}
                                          (λ _ _ → squash) pointedUnivalentStr

  PointedEqvToSIP : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvToEquivStr ] B ≃ (A ≡ B)
  PointedEqvToSIP = SIP pointedEqvToUnivalentStr

  PointedEqvTo-sip : (A B : PointedEqvTo ℓ X) → A ≃[ PointedEqvToEquivStr ] B → (A ≡ B)
  PointedEqvTo-sip A B = equivFun (PointedEqvToSIP A B)
