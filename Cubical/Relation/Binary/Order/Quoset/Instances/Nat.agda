module Cubical.Relation.Binary.Order.Quoset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_<_ to _<ℕ_)

open import Cubical.Relation.Binary.Order.Quoset.Base

open QuosetStr

ℕ<Quoset : Quoset ℓ-zero ℓ-zero
fst ℕ<Quoset = ℕ
_<_ (snd ℕ<Quoset) = _<ℕ_
isQuoset (snd ℕ<Quoset) = isQuosetℕ<
  where
    open IsQuoset
    abstract
      isQuosetℕ< : IsQuoset _<ℕ_
      isQuosetℕ< .is-set         = isSetℕ
      isQuosetℕ< .is-prop-valued = λ _ _ → isProp≤
      isQuosetℕ< .is-irrefl      = λ _ → ¬m<m
      isQuosetℕ< .is-trans       = λ _ _ _ → <-trans
      isQuosetℕ< .is-asym        = λ a b a<b b<a → ¬m<m (<-trans a<b b<a)
