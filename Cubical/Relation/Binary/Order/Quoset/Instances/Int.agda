module Cubical.Relation.Binary.Order.Quoset.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_<_ to _<ℤ_)

open import Cubical.Relation.Binary.Order.Quoset.Base

open QuosetStr

ℤ<Quoset : Quoset ℓ-zero ℓ-zero
fst ℤ<Quoset = ℤ
_<_ (snd ℤ<Quoset) = _<ℤ_
isQuoset (snd ℤ<Quoset) = isQuosetℤ<
  where
    open IsQuoset
    abstract
      isQuosetℤ< : IsQuoset _<ℤ_
      isQuosetℤ< .is-set         = isSetℤ
      isQuosetℤ< .is-prop-valued = λ _ _ → isProp<
      isQuosetℤ< .is-irrefl      = λ _ → isIrrefl<
      isQuosetℤ< .is-trans       = λ _ _ _ → isTrans<
      isQuosetℤ< .is-asym        = λ a b a<b b<a → isIrrefl< (isTrans< a<b b<a)
