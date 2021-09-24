{-# OPTIONS --cubical #-}
module Cubical.Algebra.CommMonoid.Ordered where
{-
  Definition of an ordered monoid. This is used in the construction
  of the upper naturals.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Algebra.CommMonoid.Base

open import Cubical.Relation.Binary.Poset


private
  variable
    ℓ ℓ' : Level

record IsOrderedCMonoid {M : Type ℓ} (_·_ : M → M → M) (1m : M) (_≤_ : M → M → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isPoset     : IsPoset _≤_
    isCMonoid   : IsCommMonoid 1m _·_
    isInvariant : (x y z : M) → x ≤ y → (x · z) ≤ (y · z)


record OrderedCMonoidStr (ℓ' : Level) (M : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    _≤_ : M → M → Type ℓ'
    _·_ : M → M → M
    1m : M
    isOrderedCMonoid : IsOrderedCMonoid _·_ 1m _≤_

  open IsOrderedCMonoid isOrderedCMonoid public

OrderedCMonoid : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
OrderedCMonoid ℓ ℓ' = TypeWithStr ℓ (OrderedCMonoidStr ℓ')
