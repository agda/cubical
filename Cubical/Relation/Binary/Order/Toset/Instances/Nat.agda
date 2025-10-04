module Cubical.Relation.Binary.Order.Toset.Instances.Nat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)

open import Cubical.Relation.Binary.Order.Toset

open TosetStr

ℕ≤Toset : Toset ℓ-zero ℓ-zero
fst ℕ≤Toset = ℕ
_≤_ (snd ℕ≤Toset) = _≤ℕ_
isToset (snd ℕ≤Toset) = isTosetℕ≤
  where
    open IsToset
    abstract
      isTosetℕ≤ : IsToset _≤ℕ_
      isTosetℕ≤ .is-set         = isSetℕ
      isTosetℕ≤ .is-prop-valued = λ _ _ → isProp≤
      isTosetℕ≤ .is-refl        = λ _ → ≤-refl
      isTosetℕ≤ .is-trans       = λ _ _ _ → ≤-trans
      isTosetℕ≤ .is-antisym     = λ _ _ → ≤-antisym
      isTosetℕ≤ .is-total a b with splitℕ-≤ a b
      ... | inl a≤b = ∣ inl a≤b ∣₁
      ... | inr b<a = ∣ inr (<-weaken b<a) ∣₁
