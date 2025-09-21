module Cubical.Relation.Binary.Order.StrictOrder.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_<_ to _<ℤ_)

open import Cubical.Relation.Binary.Order.StrictOrder.Base

open StrictOrderStr

ℤ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
fst ℤ<StrictOrder = ℤ
_<_ (snd ℤ<StrictOrder) = _<ℤ_
isStrictOrder (snd ℤ<StrictOrder) = isStrictOrderℤ<
  where
    open IsStrictOrder
    abstract
      isStrictOrderℤ< : IsStrictOrder _<ℤ_
      isStrictOrderℤ< .is-set           = isSetℤ
      isStrictOrderℤ< .is-prop-valued   = λ _ _ → isProp<
      isStrictOrderℤ< .is-irrefl        = λ _ → isIrrefl<
      isStrictOrderℤ< .is-trans         = λ _ _ _ → isTrans<
      isStrictOrderℤ< .is-asym          = λ a b a<b b<a → isIrrefl< (isTrans< a<b b<a)
      isStrictOrderℤ< .is-weakly-linear a b c a<b with a ≟ c
      ... | lt a<c = ∣ inl a<c ∣₁
      ... | eq a≡c = ∣ inr (subst (_<ℤ b) a≡c a<b) ∣₁
      ... | gt c<a = ∣ inr (isTrans< c<a a<b) ∣₁
