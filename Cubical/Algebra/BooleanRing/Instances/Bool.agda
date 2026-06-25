
module Cubical.Algebra.BooleanRing.Instances.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.BooleanRing.Base
open import Cubical.Data.Bool renaming (elim to bool-ind)
open import Cubical.Algebra.CommRing

open BooleanRingStr
open IsBooleanRing

BoolBRStr : BooleanRingStr Bool
𝟘 BoolBRStr   = false
𝟙 BoolBRStr   = true
_+_ BoolBRStr = _⊕_
_·_ BoolBRStr = _and_
- BoolBRStr   = λ x → x
isCommRing (isBooleanRing BoolBRStr) = makeIsCommRing
  isSetBool ⊕-assoc ⊕-identityʳ
  (bool-ind refl refl) ⊕-comm and-assoc
  and-identityʳ (bool-ind (λ _ _ → refl)
  (λ _ _ → refl)) and-comm
·Idem (isBooleanRing BoolBRStr) = bool-ind refl refl

BoolBR : BooleanRing ℓ-zero
BoolBR = Bool , BoolBRStr

