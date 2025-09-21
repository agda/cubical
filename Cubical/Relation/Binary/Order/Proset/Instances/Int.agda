module Cubical.Relation.Binary.Order.Proset.Instances.Int where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int
open import Cubical.Data.Int.Order renaming (_≤_ to _≤ℤ_)

open import Cubical.Relation.Binary.Order.Proset

open ProsetStr

ℤ≤Proset : Proset ℓ-zero ℓ-zero
fst ℤ≤Proset = ℤ
_≲_ (snd ℤ≤Proset) = _≤ℤ_
isProset (snd ℤ≤Proset) = isProsetℤ≤
  where
    open IsProset
    abstract
      isProsetℤ≤ : IsProset _≤ℤ_
      isProsetℤ≤ .is-set         = isSetℤ
      isProsetℤ≤ .is-prop-valued = λ _ _   → isProp≤
      isProsetℤ≤ .is-refl        = λ _     → isRefl≤
      isProsetℤ≤ .is-trans       = λ _ _ _ → isTrans≤
