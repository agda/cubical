module Cubical.Relation.Binary.Order.Poset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Relation.Binary.Order.Poset

open PosetStr

ℕ≤Poset : Poset ℓ-zero ℓ-zero
fst ℕ≤Poset = ℕ
_≤_ (snd ℕ≤Poset) = _≤ℕ_
isPoset (snd ℕ≤Poset) = isPosetℕ≤
  where
    open IsPoset
    abstract
      isPosetℕ≤ : IsPoset _≤ℕ_
      isPosetℕ≤ .is-set         = isSetℕ
      isPosetℕ≤ .is-prop-valued = λ _ _   → isProp≤
      isPosetℕ≤ .is-refl        = λ _     → ≤-refl
      isPosetℕ≤ .is-trans       = λ _ _ _ → ≤-trans
      isPosetℕ≤ .is-antisym     = λ _ _   → ≤-antisym
