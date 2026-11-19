module Cubical.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_) hiding (isInv→#0)

open import Cubical.Algebra.Field.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedField.Base

open OrderedFieldStr
open OrderedCommRingStr

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
fst ℚOrderedField = ℚ
0f  (snd ℚOrderedField) = 0
1f  (snd ℚOrderedField) = 1
_+_ (snd ℚOrderedField) = _+ℚ_
_·_ (snd ℚOrderedField) = _·ℚ_
-_  (snd ℚOrderedField) = -ℚ_
_<_ (snd ℚOrderedField) = _<ℚ_
_≤_ (snd ℚOrderedField) = _≤ℚ_
isOrderedField (snd ℚOrderedField) = isOrderedFieldℚ
  where
  open IsOrderedField

  isOrderedFieldℚ : IsOrderedField 0 1 _+ℚ_ _·ℚ_ -ℚ_ _<ℚ_ _≤ℚ_
  isOrderedFieldℚ .isOrderedCommRing = isOrderedCommRing $ snd ℚOrderedCommRing
  isOrderedFieldℚ .#0→isInv = λ x → hasInverseℚ x ∘ (ℚ.isIrrefl# 0 ∘_) ∘ flip subst#L
  isOrderedFieldℚ .isInv→#0 = ℚ.isInv→#0
