module Cubical.Relation.Binary.Order.Poset.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Poset

open PosetStr

ℤ≤Poset : Poset ℓ-zero ℓ-zero
fst ℤ≤Poset = ℤ
_≤_ (snd ℤ≤Poset) = _≤ℤ_
isPoset (snd ℤ≤Poset) = isPosetℤ≤
  where
    open IsPoset
    abstract
      isPosetℤ≤ : IsPoset _≤ℤ_
      isPosetℤ≤ .is-set         = isSetℤ
      isPosetℤ≤ .is-prop-valued = λ _ _ → isProp≤
      isPosetℤ≤ .is-refl        = λ _ → isRefl≤
      isPosetℤ≤ .is-trans       = λ _ _ _ → isTrans≤
      isPosetℤ≤ .is-antisym     = λ _ _ → isAntisym≤
