module Cubical.Algebra.OrderedCommMonoid.Base where
{-
  Definition of an ordered monoid.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩; str)

open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Relation.Binary.Order.Poset

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

  open IsPoset isPoset public
  open IsCommMonoid isCommMonoid public
    hiding (is-set)

record OrderedCommMonoidStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    _≤_ : M → M → Type ℓ'
    _·_ : M → M → M
    ε : M
    isOrderedCommMonoid : IsOrderedCommMonoid _·_ ε _≤_

  open IsOrderedCommMonoid isOrderedCommMonoid public

  infixl 4 _≤_

OrderedCommMonoid : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCommMonoid ℓ ℓ' = TypeWithStr ℓ (OrderedCommMonoidStr ℓ')

module _
    {M : Type ℓ} {1m : M} {_·_ : M → M → M} {_≤_ : M → M → Type ℓ'}
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
  where
  open IsOrderedCommMonoid

  makeIsOrderedCommMonoid : IsOrderedCommMonoid _·_ 1m _≤_
  isCommMonoid makeIsOrderedCommMonoid = makeIsCommMonoid is-setM assoc rid comm
  isPoset makeIsOrderedCommMonoid = isposet is-setM isProp≤ isRefl isTrans isAntisym
  MonotoneR makeIsOrderedCommMonoid = rmonotone _ _ _
  MonotoneL makeIsOrderedCommMonoid = lmonotone _ _ _

module _
    {M : Type ℓ} {1m : M} {_·_ : M → M → M} {_≤_ : M → M → Type ℓ'}
    (isCommMonoid : IsCommMonoid 1m _·_)
    (isProp≤ : (x y : M) → isProp (x ≤ y))
    (isRefl : (x : M) → x ≤ x)
    (isTrans : (x y z : M) → x ≤ y → y ≤ z → x ≤ z)
    (isAntisym : (x y : M) → x ≤ y → y ≤ x → x ≡ y)
    (rmonotone : (x y z : M) → x ≤ y → (x · z) ≤ (y · z))
    (lmonotone : (x y z : M) → x ≤ y → (z · x) ≤ (z · y))
  where
  module CM = IsOrderedCommMonoid

  IsOrderedCommMonoidFromIsCommMonoid : IsOrderedCommMonoid _·_ 1m _≤_
  CM.isPoset IsOrderedCommMonoidFromIsCommMonoid =
    isposet (IsCommMonoid.is-set isCommMonoid) isProp≤ isRefl isTrans isAntisym
  CM.isCommMonoid IsOrderedCommMonoidFromIsCommMonoid = isCommMonoid
  CM.MonotoneR IsOrderedCommMonoidFromIsCommMonoid = rmonotone _ _ _
  CM.MonotoneL IsOrderedCommMonoidFromIsCommMonoid = lmonotone _ _ _

OrderedCommMonoid→CommMonoid : OrderedCommMonoid ℓ ℓ' → CommMonoid ℓ
OrderedCommMonoid→CommMonoid M .fst = M .fst
OrderedCommMonoid→CommMonoid M .snd =
  let open OrderedCommMonoidStr (M .snd)
  in commmonoidstr _ _ isCommMonoid
