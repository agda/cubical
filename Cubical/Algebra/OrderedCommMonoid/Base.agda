{-# OPTIONS --safe #-}
module Cubical.Algebra.OrderedCommMonoid.Base where
{-
  Definition of an ordered monoid.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Relation.Binary.Poset

private
  variable
    ℓ ℓ' : Level

record IsOrderedCommMonoid
       {M : Type ℓ}
       (_·_ : M → M → M) (1m : M) (_≤_ : M → M → Type ℓ') : Type (ℓ-max ℓ ℓ')
       where
  field
    isPoset     : IsPoset _≤_
    isCommMonoid   : IsCommMonoid 1m _·_
    MonotoneR  : {x y z : M} → x ≤ y → (x · z) ≤ (y · z) -- both versions, just for convenience
    MonotoneL  : {x y z : M} → x ≤ y → (z · x) ≤ (z · y)

record OrderedCommMonoidStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    _≤_ : M → M → Type ℓ'
    _·_ : M → M → M
    ε : M
    isOrderedCommMonoid : IsOrderedCommMonoid _·_ ε _≤_

  open IsOrderedCommMonoid isOrderedCommMonoid public
  open IsPoset isPoset public
  open IsCommMonoid isCommMonoid public

  infixl 4 _≤_

OrderedCommMonoid : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommMonoid ℓ ℓ' = TypeWithStr ℓ (OrderedCommMonoidStr ℓ')

module _ where
  open IsOrderedCommMonoid

  makeIsOrderedCommMonoid : {M : Type ℓ} {1m : M} {_·_ : M → M → M} {_≤_ : M → M → Type ℓ'}
                 (is-setM : isSet M)
                 (assoc : (x y z : M) → x · (y · z) ≡ (x · y) · z)
                 (rid : (x : M) → x · 1m ≡ x)
                 (lid : (x : M) → 1m · x ≡ x)
                 (comm : (x y : M) → x · y ≡ y · x)
                 (isProp≤ : (x y : M) → isProp (x ≤ y))
                 (isRefl : (x : M) → x ≤ x)
                 (isTrans : (x y z : M) → x ≤ y → y ≤ z → x ≤ z)
                 (isAntisym : (x y : M) → x ≤ y → y ≤ x → x ≡ y)
                 (rmonotone : (x y z : M) → x ≤ y → (x · z) ≤ (y · z))
                 (lmonotone : (x y z : M) → x ≤ y → (z · x) ≤ (z · y))
               → IsOrderedCommMonoid _·_ 1m _≤_
  isCommMonoid
    (makeIsOrderedCommMonoid
      is-setM assoc rid lid comm isProp≤ isRefl isTrans isAntisym rmonotone lmonotone)
    =
    makeIsCommMonoid is-setM assoc rid comm
  isPoset
    (makeIsOrderedCommMonoid
      is-setM assoc rid lid comm isProp≤ isRefl isTrans isAntisym rmonotone lmonotone)
    =
    isposet is-setM isProp≤ isRefl isTrans isAntisym
  MonotoneR
    (makeIsOrderedCommMonoid
      is-setM assoc rid lid comm isProp≤ isRefl isTrans isAntisym rmonotone lmonotone)
    =
    rmonotone _ _ _
  MonotoneL
    (makeIsOrderedCommMonoid
      is-setM assoc rid lid comm isProp≤ isRefl isTrans isAntisym rmonotone lmonotone)
    =
    lmonotone _ _ _

  IsOrderedCommMonoidFromIsCommMonoid :
    {M : Type ℓ} {1m : M} {_·_ : M → M → M} {_≤_ : M → M → Type ℓ'}
    (isCommMonoid : IsCommMonoid 1m _·_)
    (isProp≤ : (x y : M) → isProp (x ≤ y))
    (isRefl : (x : M) → x ≤ x)
    (isTrans : (x y z : M) → x ≤ y → y ≤ z → x ≤ z)
    (isAntisym : (x y : M) → x ≤ y → y ≤ x → x ≡ y)
    (rmonotone : (x y z : M) → x ≤ y → (x · z) ≤ (y · z))
    (lmonotone : (x y z : M) → x ≤ y → (z · x) ≤ (z · y))
    → IsOrderedCommMonoid _·_ 1m _≤_
  isPoset (IsOrderedCommMonoidFromIsCommMonoid isCommMonoid isProp≤ isRefl isTrans isAntisym _ _) =
    isposet (isSetFromIsCommMonoid isCommMonoid) isProp≤ isRefl isTrans isAntisym
  isCommMonoid (IsOrderedCommMonoidFromIsCommMonoid isCommMonoid _ _ _ _ _ _) = isCommMonoid
  MonotoneR (IsOrderedCommMonoidFromIsCommMonoid isCommMonoid _ _ _ _ rmonotone _) = rmonotone _ _ _
  MonotoneL (IsOrderedCommMonoidFromIsCommMonoid isCommMonoid _ _ _ _ _ lmonotone) = lmonotone _ _ _

OrderedCommMonoid→CommMonoid : OrderedCommMonoid ℓ ℓ' → CommMonoid ℓ
OrderedCommMonoid→CommMonoid (M , _) .fst = M
OrderedCommMonoid→CommMonoid
  (M , record {
         _≤_ = _;
         _·_ = _·_;
         ε = ε;
         isOrderedCommMonoid = isOrderedCommMonoid
  }) .snd
     = let open IsOrderedCommMonoid isOrderedCommMonoid
       in commmonoidstr ε _·_ isCommMonoid

isSetOrderedCommMonoid : (M : OrderedCommMonoid ℓ ℓ') → isSet ⟨ M ⟩
isSetOrderedCommMonoid M = isSetCommMonoid (OrderedCommMonoid→CommMonoid M)
