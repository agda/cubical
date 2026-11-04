{-
  The notion of Premetric Spaces as defined in
  Formalising real numbers in homotopy type theory, Gaëtan Gilbert, 2017
-}
module Cubical.Relation.Premetric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓ' ℓ'' : Level

record IsPremetric {M : Type ℓ} (_≈[_]_ : M → ℚ₊ → M → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ispremetric

  field
    isSetM        : isSet M
    isProp≈       : ∀ x y ε → isProp (x ≈[ ε ] y)
    isRefl≈       : ∀ x     ε   → x ≈[ ε ] x
    isSym≈        : ∀ x y   ε   → x ≈[ ε ] y → y ≈[ ε ] x
    isSeparated≈  : ∀ x y       → (∀ ε → x ≈[ ε ] y) → x ≡ y
    isTriangular≈ : ∀ x y z ε δ → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε +₊ δ ] z
    isRounded≈    : ∀ x y   ε   → x ≈[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ≈[ δ ] y)

unquoteDecl IsPremetricIsoΣ = declareRecordIsoΣ IsPremetricIsoΣ (quote IsPremetric)


record PremetricStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor premetricstr

  field
    _≈[_]_      : M → ℚ₊ → M → Type ℓ'
    isPremetric : IsPremetric _≈[_]_

  open IsPremetric isPremetric public

PremetricSpace : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PremetricSpace ℓ ℓ' = TypeWithStr ℓ (PremetricStr ℓ')

premetricspace : (M : Type ℓ)
               → (_≈[_]_ : M → ℚ₊ → M → Type ℓ')
               → IsPremetric _≈[_]_
               → PremetricSpace ℓ ℓ'
premetricspace M (_≈[_]_) pm = M , (premetricstr _≈[_]_ pm)

isPropIsPremetric : {M : Type ℓ} → (_≈[_]_ : M → ℚ₊ → M → Type ℓ')
                  → isProp (IsPremetric _≈[_]_)
isPropIsPremetric _≈[_]_ = isOfHLevelRetractFromIso 1
  IsPremetricIsoΣ $
  isPropΣ isPropIsSet λ isSetM →
  isPropΣ (isPropΠ3 λ _ _ _ → isPropIsProp) λ isProp≈ →
  isProp×4
    (isPropΠ2 λ _ _ → isProp≈ _ _ _)
    (isPropΠ4 λ _ _ _ _ → isProp≈ _ _ _)
    (isPropΠ3 λ _ _ _ → isSetM _ _)
    (isPropΠ6 λ _ _ _ _ _ _ → isPropΠ λ _ → isProp≈ _ _ _)
    (isPropΠ4 λ _ _ _ _ → squash₁)
