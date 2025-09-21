module Cubical.Relation.Binary.Order.Proset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Relation.Binary.Order.Proset

open ProsetStr

ℕ≤Proset : Proset ℓ-zero ℓ-zero
fst ℕ≤Proset = ℕ
_≲_ (snd ℕ≤Proset) = _≤ℕ_
isProset (snd ℕ≤Proset) = isProsetℕ≤
  where
    open IsProset
    abstract
      isProsetℕ≤ : IsProset _≤ℕ_
      isProsetℕ≤ .is-set         = isSetℕ
      isProsetℕ≤ .is-prop-valued = λ _ _   → isProp≤
      isProsetℕ≤ .is-refl        = λ _     → ≤-refl
      isProsetℕ≤ .is-trans       = λ _ _ _ → ≤-trans
